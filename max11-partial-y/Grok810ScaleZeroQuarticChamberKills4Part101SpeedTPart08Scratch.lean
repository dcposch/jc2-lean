import Lean.Elab.Tactic.Omega

/-! Shared Nat arithmetic certificates for the round-4 chamber time lane. -/

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1600 (a f : Nat)
    (q0 : 0 < a)
    (q1 : 9 * a ≤ 4 * f) :
    2 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1601 (a d e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < a + 2 * f)
    (q2 : a + 2 * d = 2 * e)
    (q3 : a + d = f) :
    2 * a + f < a + 2 * f ∧ d + e < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1602 (a d e f : Nat)
    (q0 : 3 * a > e)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * d < 2 * e)
    (q3 : d + f < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1603 (a d e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1604 (a d e f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1605 (a d e f : Nat)
    (q0 : 3 * a > e)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * d < 2 * e)
    (q3 : d + f < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1606 (a d e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1607 (a d e f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * f < a + 2 * e)
    (q2 : 3 * a > e)
    (q3 : d + f < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1608 (a d e f : Nat)
    (q0 : 3 * a > e)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * e = 2 * f)
    (q3 : d + f < 2 * e) :
    2 * a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1609 (a d e f : Nat)
    (q0 : 2 * a + f < 2 * e)
    (q1 : 3 * a > e)
    (q2 : a + 2 * e = 2 * f)
    (q3 : d + f < 2 * e) :
    3 * a + d < 2 * e ∧ 2 * a + f < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1610 (a d e f : Nat)
    (q0 : 3 * a > e)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * e = 2 * f)
    (q3 : d + f < 2 * e) :
    a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1611 (a d e f : Nat)
    (q0 : a + 2 * e = 2 * f)
    (q1 : a + f < 2 * e)
    (q2 : d + f < 2 * e) :
    2 * a + d < 2 * e ∧ a + f < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1612 (a d e f : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * e < 2 * f)
    (q3 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ a + d + e < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1613 (a d e f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + f < 2 * f)
    (q2 : a + 2 * e < 2 * f)
    (q3 : a + d < f) :
    3 * a + d < 2 * f ∧ 2 * a + f < 2 * f ∧ d + e < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1614 (a d e g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 5 * a > 2 * d)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * d = 2 * e) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1615 (a d e g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * d = 2 * e) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1616 (a d e g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * d = 2 * e) :
    4 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1617 (a d e g : Nat)
    (q0 : 3 * a + 2 * d = 2 * g)
    (q1 : 4 * a + d < e + g)
    (q2 : 5 * a > 2 * d)
    (q3 : a + 2 * d = 2 * e) :
    4 * a + d < e + g ∧ a + d + e < e + g ∧ d + g < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1618 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : a + 2 * d = 2 * e) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1619 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 9 * a ≤ 4 * e) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1620 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 13 * a ≤ 4 * g)
    (q2 : a + 2 * d = 2 * e) :
    3 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1621 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 3 * a + d < e + g) :
    3 * a + d < e + g ∧ d + e < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1622 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 5 * a ≤ 4 * d)
    (q3 : a + 2 * d = 2 * e) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1623 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 7 * a ≤ 4 * e) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1624 (a d e g : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * g)
    (q2 : a + 2 * d = 2 * e) :
    2 * a + d < e + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1625 (a d f g : Nat)
    (q0 : 2 * g < a + 2 * f)
    (q1 : 3 * a + f < 2 * f)
    (q2 : 7 * a > 2 * f)
    (q3 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ d + g < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1626 (a d f g : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + f < 2 * f ∧ d + g < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1627 (a d f g : Nat)
    (q0 : 2 * a + d + f < 2 * g)
    (q1 : 3 * a + 2 * d < 2 * g)
    (q2 : 4 * a > g)
    (q3 : 9 * a ≤ 4 * d) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1628 (a d f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + 2 * d < 2 * g)
    (q2 : 4 * a + f < 2 * g)
    (q3 : 4 * a > g) :
    4 * a + f < 2 * g ∧ 3 * d < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1629 (a d f g : Nat)
    (q0 : 2 * a + d + f < 2 * g)
    (q1 : 3 * a + 2 * d < 2 * g)
    (q2 : 4 * a > g)
    (q3 : 7 * a ≤ 4 * d) :
    3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1630 (a f g : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * g)
    (q2 : 2 * g < a + 2 * f) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1631 (a e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * f) :
    3 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1632 (a e f g : Nat)
    (q0 : 3 * a + f < 2 * f)
    (q1 : 7 * a > 2 * f)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * f) :
    3 * a + f < 2 * f ∧ e + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1633 (a e f g : Nat)
    (q0 : 7 * a > 2 * f)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * f) :
    2 * a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1634 (a e f g : Nat)
    (q0 : 7 * a > 2 * f)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * f = 2 * g)
    (q3 : e + g < 2 * f) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1635 (a f g : Nat)
    (q0 : 0 < a)
    (q1 : 11 * a ≤ 4 * g)
    (q2 : a + 2 * f = 2 * g) :
    a + f < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1636 (a e f g : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 4 * a > g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + e < g) :
    4 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1637 (a e f g : Nat)
    (q0 : 4 * a + f < 2 * g)
    (q1 : 4 * a > g)
    (q2 : a + e < g) :
    4 * a + f < 2 * g ∧ a + e + f < 2 * g ∧ f + g < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1638 (a e f g : Nat)
    (q0 : 4 * a > g)
    (q1 : 9 * a ≤ 4 * e)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + e < g) :
    3 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1639 (a e f g : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + f < 2 * g)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + e < g) :
    3 * a + f < 2 * g ∧ e + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1640 (a e f g : Nat)
    (q0 : 4 * a > g)
    (q1 : 7 * a ≤ 4 * e)
    (q2 : a + 2 * f < 2 * g)
    (q3 : a + e < g) :
    2 * a + f < 2 * g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1641 (a b c d e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : e < a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1642 (a b c d e : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : e < a + c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ a + b + e < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ d + e < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1643 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : e < a + c) :
    3 * a + b < 3 * c ∧ 2 * a + d < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ b + e < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1644 (a b c d e : Nat)
    (q0 : 2 * e < a + 2 * d)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * c < a + 2 * d)
    (q3 : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d)
    (q4 : 5 * a > 2 * d)
    (q5 : b + c < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + b + e < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ d + e < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1645 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * e < a + 2 * d)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : 3 * c < a + 2 * d)
    (q4 : a + 6 * b < 4 * d)
    (q5 : b + c < a + d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ b + e < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1646 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 3 * c < 2 * e)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1647 (a b c d e : Nat)
    (q0 : 2 * b < e)
    (q1 : 2 * c < a + e)
    (q2 : 3 * a > e)
    (q3 : 4 * a + b < 2 * e ∧ 3 * a + d < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + b < 2 * e ∧ 3 * a + d < 2 * e ∧ 2 * a + b + c < 2 * e ∧ a + 3 * b < 2 * e ∧ a + b + e < 2 * e ∧ a + c + d < 2 * e ∧ 2 * b + d < 2 * e ∧ b + 2 * c < 2 * e ∧ d + e < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1648 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * b < e)
    (q2 : 2 * c < a + e)
    (q3 : 3 * a + b < 2 * e)
    (q4 : 3 * c < 2 * e)
    (q5 : a + 2 * d < 2 * e) :
    3 * a + b < 2 * e ∧ 2 * a + d < 2 * e ∧ a + b + c < 2 * e ∧ 3 * b < 2 * e ∧ b + e < 2 * e ∧ c + d < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1649 (a b c d e : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 2 * e)
    (q2 : 3 * c < 2 * e)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    2 * a + b < 2 * e ∧ a + d < 2 * e ∧ b + c < 2 * e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1650 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1651 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1652 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1653 (a b c d e : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1654 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : f = 0) :
    ¬ (13 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1655 (a b c e g : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1656 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    4 * a + d < 2 * c + e ∧ 3 * a + b + c < 2 * c + e ∧ 2 * a + 3 * b < 2 * c + e ∧ 2 * a + b + e < 2 * c + e ∧ 2 * a + c + d < 2 * c + e ∧ a + 2 * b + d < 2 * c + e ∧ a + b + 2 * c < 2 * c + e ∧ 3 * b + c < 2 * c + e ∧ a + d + e < 2 * c + e ∧ b + c + e < 2 * c + e ∧ b + 2 * d < 2 * c + e ∧ 2 * c + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1657 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 3 * a ≤ 4 * b)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1658 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1659 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1660 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 9 * a ≤ 4 * e)
    (q3 : a + 2 * b + c < 2 * e)
    (q4 : a + 2 * d < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1661 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : f = 0) :
    ¬ (11 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1662 (a b c e g : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1663 (a b c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e)
    (q3 : a + 2 * b + c < 2 * e) :
    3 * a + d < 2 * c + e ∧ 2 * a + b + c < 2 * c + e ∧ a + 3 * b < 2 * c + e ∧ a + b + e < 2 * c + e ∧ a + c + d < 2 * c + e ∧ 2 * b + d < 2 * c + e ∧ b + 2 * c < 2 * c + e ∧ d + e < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1664 (a b c d e : Nat)
    (q0 : 2 * e = 3 * c)
    (q1 : a + 2 * b + c < 2 * e)
    (q2 : a + 2 * d < 2 * e)
    (q3 : a ≤ 4 * b) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1665 (a c d e : Nat)
    (q0 : 3 * a ≤ 4 * c)
    (q1 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1666 (a c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 5 * a ≤ 4 * d)
    (q3 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1667 (a c d e : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : 7 * a ≤ 4 * e)
    (q3 : a + 2 * d < 2 * e) :
    2 * a + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1668 (a b c e f : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : f = 0) :
    ¬ (9 * a ≤ 4 * f) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1669 (a b c e g : Nat)
    (q0 : 2 * c < a + e)
    (q1 : 2 * e = 3 * c)
    (q2 : a + 2 * b + c < 2 * e)
    (q3 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1670 (a b c d e : Nat)
    (q0 : 2 * a + d < 2 * c + e)
    (q1 : 2 * c < a + e)
    (q2 : 2 * e = 3 * c)
    (q3 : a + 2 * b + c < 2 * e) :
    2 * a + d < 2 * c + e ∧ a + b + c < 2 * c + e ∧ 3 * b < 2 * c + e ∧ b + e < 2 * c + e ∧ c + d < 2 * c + e := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1671 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1672 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + b < a + b + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1673 (a b c d f : Nat)
    (q0 : 2 * a + b < a + b + f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    2 * a + b < a + b + f ∧ a + d < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1674 (a b c d f : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1675 (a b c d f : Nat)
    (q0 : 4 * a + b < a + b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1676 (a b c d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b) :
    3 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1677 (a b c d f : Nat)
    (q0 : 3 * a + b < a + b + f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1678 (a b c d f : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f)
    (q3 : d < a + b) :
    2 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1679 (a b c d f : Nat)
    (q0 : 2 * a + b < a + b + f)
    (q1 : b + c < f)
    (q2 : d < a + b)
    (q3 : f < 2 * a + b) :
    2 * a + b < a + b + f ∧ a + d < a + b + f ∧ b + c < a + b + f ∧ f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1680 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1681 (a b c f : Nat)
    (q0 : 7 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1682 (a b c d f : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1683 (a b c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1684 (a b c d f : Nat)
    (q0 : 4 * a + f < a + 2 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ b + d + f < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1685 (a b c f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1686 (a b c f : Nat)
    (q0 : 5 * a ≤ 4 * c)
    (q1 : a + 2 * b = 2 * c)
    (q2 : b + c < f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1687 (a b c d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1688 (a b c d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1689 (a b c d f : Nat)
    (q0 : 3 * a + f < a + 2 * f)
    (q1 : a + 2 * b = 2 * c)
    (q2 : a + b = d)
    (q3 : b + c < f)
    (q4 : b + f = 2 * d) :
    3 * a + b + c < a + 2 * f ∧ 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + c + d < a + 2 * f ∧ a + 2 * b + d < a + 2 * f ∧ a + b + 2 * c < a + 2 * f ∧ 3 * b + c < a + 2 * f ∧ a + c + f < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + 2 * d < a + 2 * f ∧ 2 * c + d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1690 (a b c d f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : d < a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1691 (a b c d f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 3 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : d < a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1692 (a b d f : Nat)
    (q0 : 5 * a ≤ 4 * b)
    (q1 : a + 4 * b < 2 * f) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1693 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1694 (a b d f : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1695 (a b d e f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b)
    (q3 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1696 (a b d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    4 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1697 (a b d f g : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b)
    (q3 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1698 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 4 * a + d < a + d + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    4 * a + d < a + d + f ∧ 3 * a + b + c < a + d + f ∧ 2 * a + 3 * b < a + d + f ∧ 3 * a + f < a + d + f ∧ 2 * a + c + d < a + d + f ∧ a + 2 * b + d < a + d + f ∧ a + b + 2 * c < a + d + f ∧ 3 * b + c < a + d + f ∧ a + c + f < a + d + f ∧ 2 * b + f < a + d + f ∧ b + 2 * d < a + d + f ∧ 2 * c + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1699 (a b d f : Nat)
    (q0 : 3 * a ≤ 4 * b)
    (q1 : a + 4 * b < 2 * f) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1700 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1701 (a b d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1702 (a b d e f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b)
    (q3 : e = 0) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1703 (a b d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    3 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1704 (a b d f g : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b)
    (q3 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1705 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a + d < a + d + f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    3 * a + d < a + d + f ∧ 2 * a + b + c < a + d + f ∧ a + 3 * b < a + d + f ∧ 2 * a + f < a + d + f ∧ a + c + d < a + d + f ∧ 2 * b + d < a + d + f ∧ b + 2 * c < a + d + f ∧ c + f < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1706 (a b d f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : a ≤ 4 * b) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1707 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1708 (a b d f : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 4 * b < 2 * f)
    (q2 : d < a + b) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1709 (a b d e f : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b)
    (q3 : e = 0) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1710 (a b d f : Nat)
    (q0 : 9 * a ≤ 4 * f)
    (q1 : a + 4 * b < 2 * f)
    (q2 : b + f = 2 * d)
    (q3 : d < a + b) :
    2 * a + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1711 (a b d f g : Nat)
    (q0 : a + 4 * b < 2 * f)
    (q1 : b + f = 2 * d)
    (q2 : d < a + b)
    (q3 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1712 (a b c d f : Nat)
    (q0 : 2 * a + d < a + d + f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : a + 4 * b < 2 * f)
    (q3 : b + f = 2 * d)
    (q4 : d < a + b) :
    2 * a + d < a + d + f ∧ a + b + c < a + d + f ∧ 3 * b < a + d + f ∧ a + f < a + d + f ∧ c + d < a + d + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1713 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    4 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1714 (a b c d f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 4 * a + f < a + 2 * f)
    (q2 : a + 4 * b < 2 * f)
    (q3 : a + b = d)
    (q4 : b + f = 2 * d) :
    4 * a + b + c < a + 2 * f ∧ 3 * a + 3 * b < a + 2 * f ∧ 4 * a + f < a + 2 * f ∧ 3 * a + c + d < a + 2 * f ∧ 2 * a + 2 * b + d < a + 2 * f ∧ 2 * a + b + 2 * c < a + 2 * f ∧ a + 3 * b + c < a + 2 * f ∧ 5 * b < a + 2 * f ∧ 2 * a + c + f < a + 2 * f ∧ a + 2 * b + f < a + 2 * f ∧ a + b + 2 * d < a + 2 * f ∧ a + 2 * c + d < a + 2 * f ∧ 2 * b + c + d < a + 2 * f ∧ b + 3 * c < a + 2 * f ∧ b + d + f < a + 2 * f ∧ 2 * c + f < a + 2 * f ∧ 3 * d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1715 (a b c f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : a + 4 * b < 2 * f) :
    3 * a + f < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1716 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + f < a + 2 * f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : a + b = d)
    (q5 : b + f = 2 * d) :
    3 * a + b + c < a + 2 * f ∧ 2 * a + 3 * b < a + 2 * f ∧ 3 * a + f < a + 2 * f ∧ 2 * a + c + d < a + 2 * f ∧ a + 2 * b + d < a + 2 * f ∧ a + b + 2 * c < a + 2 * f ∧ 3 * b + c < a + 2 * f ∧ a + c + f < a + 2 * f ∧ 2 * b + f < a + 2 * f ∧ b + 2 * d < a + 2 * f ∧ 2 * c + d < a + 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1717 (a b c d f : Nat)
    (q0 : 2 * a + b = f)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : d < a + b) :
    4 * a + b < a + b + f ∧ 3 * a + d < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + c + d < a + b + f ∧ 2 * b + d < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1718 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b = f)
    (q2 : 2 * c < a + 2 * b)
    (q3 : 3 * a + b < a + b + f)
    (q4 : a + 4 * b < 2 * f)
    (q5 : d < a + b) :
    3 * a + b < a + b + f ∧ 2 * a + d < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ c + d < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1719 (a b c d f : Nat)
    (q0 : 2 * a > c)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : a + b + f < 3 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1720 (a b c d f : Nat)
    (q0 : 2 * a > c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : a + 2 * f < 4 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1721 (a b c d f : Nat)
    (q0 : 2 * a > c)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : a + 2 * f < 4 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1722 (a b c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * a > c)
    (q2 : a + 2 * d < 3 * c)
    (q3 : a + 2 * f < 4 * c)
    (q4 : a + b + f < 3 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1723 (a b c d f : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1724 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : a + 2 * f < 4 * c) :
    3 * a + b < 3 * c ∧ 2 * a + d < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1725 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : a + b + f < 3 * c) :
    2 * a + b < 3 * c ∧ a + d < 3 * c ∧ b + c < 3 * c ∧ f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1726 (a b c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : c + d < a + f) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1727 (a b c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : c + d < a + f) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1728 (a b c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : c + d < a + f) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1729 (a b c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * f < 3 * a + 2 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : c + d < a + f) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1730 (a b c d f : Nat)
    (q0 : 2 * f < 3 * a + 2 * c)
    (q1 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + f < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : b + c < f)
    (q4 : c + d < a + f) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ 2 * a + f < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ c + f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1731 (a b c d f : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f)
    (q3 : c + d < a + f) :
    3 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1732 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : a + 4 * d < 2 * c + 2 * f)
    (q4 : b + c < f)
    (q5 : c + d < a + f) :
    3 * a + b < 3 * c ∧ 2 * a + d < 3 * c ∧ a + b + c < 3 * c ∧ 3 * b < 3 * c ∧ a + f < 3 * c ∧ c + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1733 (a b c d f : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * f = 4 * c)
    (q2 : b + c < f)
    (q3 : c + d < a + f) :
    2 * a + b < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1734 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < 3 * c)
    (q2 : a + 2 * f = 4 * c)
    (q3 : a + 4 * d < 2 * c + 2 * f)
    (q4 : b + c < f)
    (q5 : c + d < a + f) :
    2 * a + b < 3 * c ∧ a + d < 3 * c ∧ b + c < 3 * c ∧ f < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1735 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * b < 2 * c)
    (q4 : b + c < f) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1736 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 7 * a ≤ 4 * c)
    (q4 : b + c < f) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1737 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : 9 * a ≤ 4 * d)
    (q4 : b + c < f) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1738 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : e = 0) :
    ¬ (11 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1739 (a b c d f : Nat)
    (q0 : 13 * a ≤ 4 * f)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 4 * c < a + 2 * f)
    (q4 : b + c < f) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1740 (a b c d f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : g = 0) :
    ¬ (15 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1741 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (q3 : 4 * c < a + 2 * f)
    (q4 : a + 2 * b < 2 * c)
    (q5 : b + c < f) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1742 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 3 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : b + c < f) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1743 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 5 * a ≤ 4 * c)
    (q2 : b + c < f) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1744 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 7 * a ≤ 4 * d)
    (q3 : b + c < f) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1745 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : e = 0) :
    ¬ (9 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1746 (a b c d f : Nat)
    (q0 : 11 * a ≤ 4 * f)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : b + c < f) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1747 (a b c d f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : g = 0) :
    ¬ (13 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1748 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : 4 * c < a + 2 * f)
    (q4 : b + c < f) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1749 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : a + 2 * b < 2 * c)
    (q2 : a ≤ 4 * b)
    (q3 : b + c < f) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1750 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 3 * a ≤ 4 * c)
    (q2 : b + c < f) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1751 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 5 * a ≤ 4 * d)
    (q3 : b + c < f) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1752 (a b c d e f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : e = 0) :
    ¬ (7 * a ≤ 4 * e) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1753 (a b c d f : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 9 * a ≤ 4 * f)
    (q3 : b + c < f) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1754 (a b c d f g : Nat)
    (q0 : 2 * c + 2 * f = a + 4 * d)
    (q1 : 2 * d < a + 2 * c)
    (q2 : 4 * c < a + 2 * f)
    (q3 : a + 2 * b < 2 * c)
    (q4 : g = 0) :
    ¬ (11 * a ≤ 4 * g) := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1755 (a b c d f : Nat)
    (q0 : 2 * a + b < a + 2 * d)
    (q1 : 2 * c + 2 * f = a + 4 * d)
    (q2 : 2 * d < a + 2 * c)
    (q3 : 4 * c < a + 2 * f)
    (q4 : a + 2 * b < 2 * c)
    (q5 : b + c < f) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1756 (a b c d f : Nat)
    (q0 : 2 * d < a + 2 * c)
    (q1 : 3 * a + 2 * c = 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 4 * c < a + 2 * f)
    (q4 : a + 2 * b < 2 * c)
    (q5 : b + c < f) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1757 (a b c d : Nat)
    (q0 : 2 * b + c < 2 * d)
    (q1 : 3 * c < a + 2 * d)
    (q2 : 5 * a > 2 * d)
    (q3 : 7 * a ≤ 4 * c) :
    3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1758 (a b c d f : Nat)
    (q0 : 3 * a + d < a + 2 * d ∧ 4 * a + b < a + 2 * d)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * c < a + 2 * d)
    (q3 : 4 * b < a + 2 * d)
    (q4 : 5 * a > 2 * d)
    (q5 : b + c < a + d)
    (q6 : f < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ 2 * a + f < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ c + f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1759 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 3 * a + b < a + 2 * d)
    (q2 : 3 * c < a + 2 * d)
    (q3 : a + 6 * b < 4 * d)
    (q4 : b + c < a + d)
    (q5 : f < a + d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ a + f < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1760 (a b c d f : Nat)
    (q0 : 0 < a)
    (q1 : 2 * a + b < a + 2 * d)
    (q2 : 2 * b + c < 2 * d)
    (q3 : 3 * c < a + 2 * d)
    (q4 : b + f < 2 * d) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d ∧ f < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1761 (a b c d f : Nat)
    (q0 : 2 * a + b < f)
    (q1 : 3 * a + 2 * c < 2 * f)
    (q2 : 3 * a + f < 2 * f)
    (q3 : 7 * a > 2 * f)
    (q4 : a + d < f) :
    4 * a + d < 2 * f ∧ 3 * a + b + c < 2 * f ∧ 2 * a + 3 * b < 2 * f ∧ 3 * a + f < 2 * f ∧ 2 * a + c + d < 2 * f ∧ a + 2 * b + d < 2 * f ∧ a + b + 2 * c < 2 * f ∧ 3 * b + c < 2 * f ∧ a + c + f < 2 * f ∧ 2 * b + f < 2 * f ∧ b + 2 * d < 2 * f ∧ 2 * c + d < 2 * f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1762 (a b c d g : Nat)
    (q0 : 9 * a ≤ 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    4 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1763 (a b c d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 4 * a + b < c + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1764 (a b c d g : Nat)
    (q0 : 7 * a ≤ 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1765 (a b c d g : Nat)
    (q0 : 2 * g < 5 * a + 2 * b)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1766 (a b c d g : Nat)
    (q0 : 5 * a ≤ 4 * d)
    (q1 : a + 2 * b < g)
    (q2 : a + 2 * b = 2 * c)
    (q3 : d < a + b) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1767 (a b c d g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 2 * g < 5 * a + 2 * b)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b) :
    2 * a + b < c + g ∧ a + d < c + g ∧ b + c < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1768 (a b c d g : Nat)
    (q0 : 4 * a + b < c + g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1769 (a b c d g : Nat)
    (q0 : 3 * a + b < c + g)
    (q1 : 5 * a + 2 * b = 2 * g)
    (q2 : a + 2 * b < g)
    (q3 : a + 2 * b = 2 * c)
    (q4 : d < a + b) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1770 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b < g) :
    4 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1771 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : d < a + b) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1772 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 5 * a ≤ 4 * c)
    (q3 : a + 2 * b < g) :
    3 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1773 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : d < a + b) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1774 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a ≤ 4 * c)
    (q3 : a + 2 * b < g) :
    2 * a + b < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1775 (a b c d g : Nat)
    (q0 : 2 * a + b < a + 2 * d)
    (q1 : 2 * b + 2 * g = a + 4 * d)
    (q2 : 2 * c < a + 2 * b)
    (q3 : a + 2 * b < g)
    (q4 : d < a + b) :
    2 * a + b < a + 2 * d ∧ a + d < a + 2 * d ∧ b + c < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1776 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 4 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : a + b = d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1777 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g = a + 4 * d)
    (q1 : 2 * c < a + 2 * b)
    (q2 : 3 * a + b < a + 2 * d)
    (q3 : a + 2 * b < g)
    (q4 : a + b = d) :
    3 * a + b < a + 2 * d ∧ 2 * a + d < a + 2 * d ∧ a + b + c < a + 2 * d ∧ 3 * b < a + 2 * d ∧ c + d < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1778 (a b c d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a > c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1779 (a b c d g : Nat)
    (q0 : 2 * a > c)
    (q1 : 4 * a + b < 3 * c ∧ 3 * a + d < 3 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < 3 * c)
    (q4 : g < 2 * c) :
    4 * a + b < 3 * c ∧ 3 * a + d < 3 * c ∧ 2 * a + b + c < 3 * c ∧ a + 3 * b < 3 * c ∧ a + c + d < 3 * c ∧ 2 * b + d < 3 * c ∧ b + 2 * c < 3 * c ∧ b + g < 3 * c := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1780 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * b)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1781 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * c)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1782 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 9 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1783 (a b c d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1784 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 4 * a + b < c + g ∧ 3 * a + d < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1785 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 7 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1786 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 3 * a + b < c + g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    3 * a + b < c + g ∧ 2 * a + d < c + g ∧ a + b + c < c + g ∧ 3 * b < c + g ∧ c + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1787 (a b c d g : Nat)
    (q0 : 2 * c < g)
    (q1 : 5 * a ≤ 4 * d)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    2 * a + b < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1788 (a b c d g : Nat)
    (q0 : 2 * a + b < c + g)
    (q1 : 2 * c < g)
    (q2 : a + 2 * b < 2 * c)
    (q3 : a + 2 * d < c + g)
    (q4 : g < 2 * a + c) :
    2 * a + b < c + g ∧ a + d < c + g ∧ b + c < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1789 (a b c d g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 5 * a ≤ 4 * b)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1790 (a b c d g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 7 * a ≤ 4 * c)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1791 (a b c d g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 9 * a ≤ 4 * d)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1792 (a b c d g : Nat)
    (q0 : 15 * a ≤ 4 * g)
    (q1 : 2 * a + c = g)
    (q2 : 2 * c < g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1793 (a b c d g : Nat)
    (q0 : 2 * a + c = g)
    (q1 : 2 * c < g)
    (q2 : 4 * a + b < c + g ∧ 3 * a + d < c + g)
    (q3 : a + 2 * b < 2 * c)
    (q4 : a + 2 * d < c + g) :
    4 * a + b < c + g ∧ 3 * a + d < c + g ∧ 2 * a + b + c < c + g ∧ a + 3 * b < c + g ∧ a + c + d < c + g ∧ 2 * b + d < c + g ∧ b + 2 * c < c + g ∧ b + g < c + g := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1794 (a b c d g : Nat)
    (q0 : 2 * g < 3 * a + 2 * d)
    (q1 : 3 * a > 2 * b)
    (q2 : 3 * c < a + 2 * d)
    (q3 : 4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d)
    (q4 : 5 * a > 2 * d)
    (q5 : b + c < a + d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1795 (a b c d g : Nat)
    (q0 : 2 * b + 2 * g < a + 4 * d)
    (q1 : 3 * a + 2 * d = 2 * g)
    (q2 : 3 * a + d < a + 2 * d)
    (q3 : 5 * a > 2 * d)
    (q4 : c + g < a + 2 * d) :
    4 * a + b < a + 2 * d ∧ 3 * a + d < a + 2 * d ∧ 2 * a + b + c < a + 2 * d ∧ a + 3 * b < a + 2 * d ∧ a + c + d < a + 2 * d ∧ 2 * b + d < a + 2 * d ∧ b + 2 * c < a + 2 * d ∧ b + g < a + 2 * d := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1796 (a b c e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 4 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1797 (a b c e f : Nat)
    (q0 : 2 * c < a + 2 * b)
    (q1 : 2 * e < a + b + f)
    (q2 : 3 * a + b < a + b + f)
    (q3 : a + 4 * b < 2 * f)
    (q4 : f < 2 * a + b) :
    3 * a + b < a + b + f ∧ a + b + c < a + b + f ∧ 3 * b < a + b + f ∧ a + f < a + b + f ∧ b + e < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1798 (a b c e f : Nat)
    (q0 : 11 * a ≤ 4 * e)
    (q1 : 2 * e < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f := by
  omega
set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic certificate for chamber degree bands. -/
theorem astra4u_Round4Package_nat_1799 (a b c e f : Nat)
    (q0 : 2 * e < a + b + f)
    (q1 : 4 * a + b < a + b + f)
    (q2 : a + 2 * b = 2 * c)
    (q3 : b + c < f)
    (q4 : f < 2 * a + b) :
    4 * a + b < a + b + f ∧ 2 * a + b + c < a + b + f ∧ a + 3 * b < a + b + f ∧ 2 * a + f < a + b + f ∧ a + b + e < a + b + f ∧ b + 2 * c < a + b + f ∧ c + f < a + b + f := by
  omega

end Max11DegreeRoutes
