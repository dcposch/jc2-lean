import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1400 (a b e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1401 (a b e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1402 (a b e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 3 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1403 (a b e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1404 (a b e f : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : b + e < a + f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1405 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : b + e < a + f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1406 (a b e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + b + f = 2 * e)
    (q3 : b + e < a + f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1407 (a b e f : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 3 * a + f < 2 * f)
    (q2 : a + b + f = 2 * e)
    (q3 : b + e < a + f) :
    2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ 2 * b + f < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1408 (a b e f : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : b + e < a + f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1409 (a b e f : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : b + e < a + f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1410 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + b + f = 2 * e)
    (q3 : b + e < a + f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1411 (a b e f : Nat)
    (q0 : 2 * a + f < 2 * f)
    (q1 : a + b + f = 2 * e)
    (q2 : b + e < a + f) :
    a + 3 * b < 2 * f ∧ 2 * a + f < 2 * f ∧ a + b + e < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1412 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a + b = f)
    (q2 : 2 * e < a + b + f)
    (q3 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1413 (a b e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1414 (a b e f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * e < a + b + f)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 4 * b < 2 * f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1415 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 2 * e < a + b + f)
    (q3 : 3 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f) :
    3 * a + b < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1416 (a b e f : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a + 6 * b < 4 * e)
    (q2 : 3 * a > e)
    (q3 : 5 * a ≤ 4 * b)
    (q4 : a + b + f < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1417 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * b < e)
    (q2 : 2 * f < a + 2 * e)
    (q3 : 3 * a > e) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1418 (a b e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + b + f < 2 * e) :
    4 * a + b < 2 * e ∧ 2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1419 (a b e f : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a > e)
    (q2 : 4 * a + b < 2 * e ∧ 2 * a + f < 2 * e) :
    4 * a + b < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1420 (a b e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + b + f < 2 * e) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1421 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 3 * a + b < 2 * e)
    (q3 : a + b + f < 2 * e) :
    3 * a + b < 2 * e ∧ 3 * b < 2 * e ∧ a + f < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1422 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 9 * a ≤ 4 * f)
    (q2 : a + b + f < 2 * e) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1423 (a b e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 2 * e)
    (q2 : a + b + f < 2 * e) :
    2 * a + b < 2 * e ∧ f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1424 (a b e f : Nat)
    (q0 : 3 * a > e)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * e = 2 * f)
    (q3 : a + b + f < 2 * e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1425 (a e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * e = 2 * f) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1426 (a e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 3 * a > e)
    (q2 : a + 2 * e = 2 * f) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1427 (a b e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * e = 2 * f)
    (q3 : a + b + f < 2 * e) :
    4 * a + b < 2 * e ∧ a + 3 * b < 2 * e ∧ 2 * a + f < 2 * e ∧ a + b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1428 (a b e f : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * e < 2 * f) :
    2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + b + e < 2 * f ∧ 2 * b + f < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1429 (a b e g : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1430 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : c = 0) :
    ¬ (7 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1431 (a b d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : d = 0) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1432 (a b e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1433 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1434 (a b e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1435 (a b e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 4 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    4 * a + b < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1436 (a b e g : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1437 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : c = 0) :
    ¬ (5 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1438 (a b d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : d = 0) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1439 (a b e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1440 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : f = 0) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1441 (a b e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1442 (a b e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 3 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    3 * a + b < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1443 (a b e g : Nat)
    (q0 : a + 2 * b + 2 * g = 4 * e)
    (q1 : a + 2 * b < g)
    (q2 : a ≤ 4 * b) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1444 (a b c e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : c = 0) :
    ¬ (3 * a ≤ 4 * c) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1445 (a b d e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : d = 0) :
    ¬ (5 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1446 (a b e g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1447 (a b e f g : Nat)
    (q0 : 2 * e < 3 * a + 2 * b)
    (q1 : a + 2 * b + 2 * g = 4 * e)
    (q2 : a + 2 * b < g)
    (q3 : f = 0) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1448 (a b e g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * e < 3 * a + 2 * b)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1449 (a b e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1450 (a b e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1451 (a b e g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 4 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    4 * a + b < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1452 (a b e g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1453 (a b e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 3 * a + 2 * b = 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1454 (a b e g : Nat)
    (q0 : 3 * a + 2 * b = 2 * e)
    (q1 : 3 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g = 4 * e)
    (q3 : a + 2 * b < g) :
    3 * a + b < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1455 (a b e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * b < e)
    (q2 : 3 * a > e)
    (q3 : g < a + e) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1456 (a b e g : Nat)
    (q0 : 2 * b < e)
    (q1 : 3 * a > e)
    (q2 : 4 * a + b < 2 * e)
    (q3 : g < a + e) :
    4 * a + b < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1457 (a b e g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * b < e)
    (q2 : 3 * a > e)
    (q3 : g < a + e) :
    3 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1458 (a b e g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * b < e)
    (q2 : 3 * a > e)
    (q3 : g < a + e) :
    2 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1459 (a b e g : Nat)
    (q0 : 3 * a > e)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + e = g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1460 (a b e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + e = g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1461 (a b e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a > e)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + e = g) :
    4 * a + b < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1462 (a b e g : Nat)
    (q0 : 3 * a > e)
    (q1 : 4 * a + b < 2 * e)
    (q2 : a + 2 * b + 2 * g < 4 * e)
    (q3 : a + e = g) :
    4 * a + b < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ b + g < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1463 (a b f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1464 (a b f g : Nat)
    (q0 : 2 * g < a + 2 * f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + g < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1465 (a b f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1466 (a b f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1467 (a b f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1468 (a b f g : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + g < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1469 (a b f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1470 (a b f g : Nat)
    (q0 : 11 * a ≤ 4 * g)
    (q1 : a + 2 * f = 2 * g)
    (q2 : a + 4 * b < 2 * f)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1471 (a b f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a + b = f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1472 (a b f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + g < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1473 (a b f g : Nat)
    (q0 : 0 < a)
    (q1 : 13 * a ≤ 4 * g)
    (q2 : a + 2 * f = 2 * g) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1474 (a b f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a + b = f)
    (q2 : 2 * g < a + 2 * f)
    (q3 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1475 (a b f g : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f) :
    4 * a + b < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ b + g < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1476 (a b f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * a + b = f)
    (q2 : 2 * g < a + 2 * f)
    (q3 : a + 4 * b < 2 * f) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1477 (a b f g : Nat)
    (q0 : 5 * a + 2 * b = 2 * g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < g)
    (q3 : f < 2 * a + b) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1478 (a b f g : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : f < 2 * a + b) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1479 (a b f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : f < 2 * a + b) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1480 (a b f g : Nat)
    (q0 : 0 < a)
    (q1 : 4 * a + f < 2 * g)
    (q2 : 5 * a + 2 * b = 2 * g)
    (q3 : a + 2 * b < g) :
    3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 5 * b < 2 * g ∧ a + 2 * b + f < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1481 (a f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 7 * a > 2 * f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1482 (a f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1483 (a b f g : Nat)
    (q0 : 3 * a + b + f < 2 * g)
    (q1 : 4 * a > g)
    (q2 : 5 * a + 2 * b < 2 * g)
    (q3 : 5 * a ≤ 4 * b) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1484 (a b f g : Nat)
    (q0 : 0 < a)
    (q1 : 4 * a + f < 2 * g)
    (q2 : 4 * a > g)
    (q3 : 5 * a + 2 * b < 2 * g) :
    3 * a + 3 * b < 2 * g ∧ 4 * a + f < 2 * g ∧ 5 * b < 2 * g ∧ a + 2 * b + f < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1485 (a c d e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a > c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : e < a + c) :
    3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1486 (a c d e : Nat)
    (q0 : 2 * a > c)
    (q1 : 3 * a + d < 3 * c)
    (q2 : e < a + c) :
    3 * a + d < 3 * c ∧ a + c + d < 3 * c ∧ d + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1487 (a c d e : Nat)
    (q0 : 2 * a > c)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * d < 3 * c)
    (q3 : e < a + c) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1488 (a c d e : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 3 * a + d < a + 2 * d)
    (q2 : 3 * c < a + 2 * d)
    (q3 : 5 * a > 2 * d) :
    3 * a + d < a + 2 * d ∧ a + c + d < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1489 (a c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1490 (a c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 3 * a + d < 2 * e)
    (q2 : 3 * a > e) :
    3 * a + d < 2 * e ∧ a + c + d < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1491 (a c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1492 (a c d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < 2 * e)
    (q2 : 3 * c < 2 * e)
    (q3 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1493 (a c d f : Nat)
    (q0 : 2 * a > c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : a + 2 * f < 4 * c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1494 (a c d f : Nat)
    (q0 : 2 * a > c)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * d < 3 * c)
    (q3 : a + 2 * f < 4 * c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1495 (a c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * a > c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : a + 2 * f < 4 * c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1496 (a c d f : Nat)
    (q0 : 2 * a > c)
    (q1 : 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c ∧ a + c + d < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1497 (a c d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * a > c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : a + 2 * f < 4 * c) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1498 (a c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < 3 * c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : a + 2 * f < 4 * c) :
    2 * a + d < 3 * c ∧ a + f < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1499 (a c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : c + d < a + f) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1500 (a c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * f = 4 * c)
    (q3 : c + d < a + f) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1501 (a c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : c + d < a + f) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1502 (a c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : c + d < a + f) :
    3 * a + d < 3 * c ∧ 2 * a + f < 3 * c ∧ a + c + d < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1503 (a c d f : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * f = 4 * c)
    (q2 : c + d < a + f) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1504 (a c d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * f = 4 * c)
    (q2 : c + d < a + f) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1505 (a c d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : c + d < a + f) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1506 (a c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : c + d < a + f) :
    2 * a + d < 3 * c ∧ a + f < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1507 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 7 * a ≤ 4 * c) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1508 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 9 * a ≤ 4 * d) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1509 (a c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 4 * c < a + 2 * f) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1510 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + d < a + 2 * d)
    (q3 : 4 * c < a + 2 * f) :
    3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1511 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 5 * a ≤ 4 * c) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1512 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 7 * a ≤ 4 * d) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1513 (a c d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 4 * c < a + 2 * f) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1514 (a c d f : Nat)
    (q0 : 2 * a + d < a + 2 * d)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 4 * c < a + 2 * f) :
    2 * a + d < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1515 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a ≤ 4 * c)
    (q3 : 4 * c < a + 2 * f) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1516 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 5 * a ≤ 4 * d) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1517 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 9 * a ≤ 4 * f) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1518 (a c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : a + d < a + 2 * d) :
    a + d < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1519 (a c d f : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * c < a + 2 * f)
    (q2 : 9 * a ≤ 4 * d) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1520 (a c d f : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 4 * c < a + 2 * f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + c + f < 2 * f ∧ 2 * c + d < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1521 (a c d f : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 4 * c < a + 2 * f)
    (q2 : 7 * a ≤ 4 * d) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1522 (a c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 3 * a + 2 * c = 2 * f) :
    3 * a + d < 2 * f ∧ 2 * a + f < 2 * f ∧ a + c + d < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1523 (a c d f : Nat)
    (q0 : 3 * a + d < a + 2 * d)
    (q1 : 3 * c < a + 2 * d)
    (q2 : 5 * a > 2 * d)
    (q3 : f < a + d) :
    3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1524 (a c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < a + 2 * d)
    (q2 : 3 * c < a + 2 * d)
    (q3 : f < a + d) :
    2 * a + d < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1525 (a c d f : Nat)
    (q0 : 3 * a + 2 * c < 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + c + f < 2 * f ∧ 2 * c + d < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1526 (a c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : 3 * a + 2 * c < 2 * f)
    (q3 : a + d < f) :
    3 * a + d < 2 * f ∧ 2 * a + f < 2 * f ∧ a + c + d < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1527 (a c d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : g < 2 * c) :
    3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1528 (a c d g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : g < 2 * c) :
    2 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1529 (a d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * g < 3 * a + 2 * d)
    (q2 : 5 * a > 2 * d) :
    3 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1530 (a d g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * g < 3 * a + 2 * d)
    (q2 : 5 * a > 2 * d) :
    2 * a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1531 (a d g : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * g)
    (q2 : 2 * g < 3 * a + 2 * d) :
    a + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1532 (a c d g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 3 * a + d < a + 2 * d)
    (q2 : 5 * a > 2 * d)
    (q3 : c + g < a + 2 * d) :
    3 * a + d < a + 2 * d ∧ a + c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1533 (a c d g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + d < a + 2 * d)
    (q2 : 3 * a + 2 * d = 2 * g)
    (q3 : c + g < a + 2 * d) :
    2 * a + d < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1534 (a c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a > c)
    (q2 : a + 2 * f < 4 * c)
    (q3 : e < a + c) :
    2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1535 (a c e f : Nat)
    (q0 : 2 * a > c)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * f < 4 * c)
    (q3 : e < a + c) :
    a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1536 (a c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : e < a + c) :
    2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1537 (a c e f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : e < a + c) :
    a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1538 (a b c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b = 0)
    (q3 : e < a + c) :
    ¬ (5 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1539 (a c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1540 (a c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : d = 0)
    (q3 : e < a + c) :
    ¬ (9 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1541 (a c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1542 (a c e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1543 (a c e f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : e < a + c)
    (q3 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1544 (a c e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    2 * a + f < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1545 (a b c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : b = 0)
    (q3 : e < a + c) :
    ¬ (3 * a ≤ 4 * b) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1546 (a c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1547 (a c d e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : d = 0)
    (q3 : e < a + c) :
    ¬ (7 * a ≤ 4 * d) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1548 (a c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1549 (a c e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : e < a + c) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1550 (a c e f g : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : a + 2 * c + 2 * f = 4 * e)
    (q2 : e < a + c)
    (q3 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1551 (a c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1552 (a c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1553 (a c e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1554 (a c e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e) :
    2 * a + f < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1555 (a c e f : Nat)
    (q0 : 0 < a)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f = 4 * e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1556 (a c e f : Nat)
    (q0 : 0 < a)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1557 (a c e f : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * f)
    (q2 : a + 2 * c + 2 * f = 4 * e)
    (q3 : a + c = e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1558 (a c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * c < a + 2 * f)
    (q2 : e < a + c) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1559 (a c e f : Nat)
    (q0 : 3 * a + 2 * c = 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 4 * c < a + 2 * f)
    (q3 : e < a + c) :
    3 * a + f < 2 * f ∧ a + c + f < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1560 (a c e f : Nat)
    (q0 : 4 * c < a + 2 * f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : e < a + c) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1561 (a c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 7 * a ≤ 4 * c) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1562 (a e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1563 (a e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1564 (a c e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 2 * c < a + e)
    (q2 : 3 * a > e) :
    2 * a + f < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1565 (a c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 5 * a ≤ 4 * c) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1566 (a e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 9 * a ≤ 4 * e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1567 (a e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1568 (a c e f : Nat)
    (q0 : 3 * a > e)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f < 4 * e)
    (q3 : a + 2 * e = 2 * f) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1569 (a c e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * c + 2 * f < 4 * e)
    (q3 : a + 2 * e = 2 * f) :
    2 * a + f < 2 * e ∧ c + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1570 (a c e f : Nat)
    (q0 : 3 * a > e)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 2 * c + 2 * f < 4 * e)
    (q3 : a + 2 * e = 2 * f) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1571 (a e f : Nat)
    (q0 : 0 < a)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * e = 2 * f) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1572 (a e f : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * f)
    (q2 : a + 2 * e = 2 * f) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1573 (a c e f : Nat)
    (q0 : 3 * a + 2 * c < 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + 2 * e < 2 * f) :
    3 * a + f < 2 * f ∧ a + c + f < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1574 (a c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * f < 4 * c)
    (q3 : g < 2 * c) :
    2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1575 (a c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * f < 4 * c)
    (q3 : g < 2 * c) :
    a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1576 (a c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : 2 * g < a + 2 * f) :
    2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1577 (a c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : 2 * g < a + 2 * f) :
    a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1578 (a c f g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : g < 2 * a + c) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1579 (a c f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 4 * c < a + 2 * f)
    (q2 : g < 2 * a + c) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1580 (a f g : Nat)
    (q0 : 13 * a ≤ 4 * g)
    (q1 : 2 * g < a + 2 * f)
    (q2 : 7 * a > 2 * f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1581 (a c f g : Nat)
    (q0 : 7 * a > 2 * f)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + c + g < 2 * f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1582 (a c f g : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + c + g < 2 * f) :
    3 * a + f < 2 * f ∧ a + c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1583 (a c f g : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + c + g < 2 * f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1584 (a f g : Nat)
    (q0 : 0 < a)
    (q1 : 13 * a ≤ 4 * g)
    (q2 : a + 2 * f = 2 * g) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1585 (a c f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + c + g < 2 * f) :
    2 * a + f < 2 * f ∧ c + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1586 (a c f g : Nat)
    (q0 : 2 * a + c < g)
    (q1 : 4 * a > g)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * f < 2 * g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1587 (a c f g : Nat)
    (q0 : 2 * a + c < g)
    (q1 : 4 * a + f < 2 * g)
    (q2 : 4 * a > g) :
    4 * a + f < 2 * g ∧ 2 * a + c + f < 2 * g ∧ 2 * c + f < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1588 (a c f g : Nat)
    (q0 : 2 * a + c < g)
    (q1 : 4 * a > g)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * f < 2 * g) :
    3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1589 (a c f g : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + c < g)
    (q2 : 3 * a + f < 2 * g)
    (q3 : a + 2 * f < 2 * g) :
    3 * a + f < 2 * g ∧ a + c + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1590 (a d e f : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 3 * a + d < a + 2 * d)
    (q2 : 5 * a > 2 * d)
    (q3 : f < a + d) :
    3 * a + d < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1591 (a d f : Nat)
    (q0 : 5 * a > 2 * d)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + d = f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1592 (a d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 5 * a > 2 * d)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1593 (a d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 5 * a > 2 * d)
    (q2 : a + d = f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1594 (a d e f : Nat)
    (q0 : 4 * a + f < a + 2 * f)
    (q1 : 5 * a > 2 * d)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f) :
    4 * a + f < a + 2 * f ∧ 2 * a + d + e < a + 2 * f ∧ a + e + f < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1595 (a d f : Nat)
    (q0 : 0 < a)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + d = f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1596 (a d e f : Nat)
    (q0 : 0 < a)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1597 (a d e f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + f < a + 2 * f)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f) :
    3 * a + f < a + 2 * f ∧ a + d + e < a + 2 * f ∧ e + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1598 (a d f : Nat)
    (q0 : 0 < a)
    (q1 : 5 * a ≤ 4 * d)
    (q2 : a + d = f) :
    2 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1599 (a d e f : Nat)
    (q0 : 0 < a)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f) :
    2 * a + f < a + 2 * f := by
  omega

end Max11DegreeRoutes
