import LowScale68SecondaryFace

/-! # Extracting the first `(6,8)` secondary face

This module connects the abstract scalar face classified in
`LowScale68SecondaryFace` to the literal polynomial lower system.  The four
transverse coordinates have different secondary degree bounds, so the usual
single weighted-boundary lemmas are first replaced by arbitrary-bound
coefficient rules.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryExtraction68

variable {k : Type*} [Field k] [CharZero k]

/-- A product has the expected coefficient at the sum of arbitrary separate
degree bounds. -/
theorem coeff_mul_at_bounds68 (p q : k[X]) (u v : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (p * q).coeff (u + v) = p.coeff u * q.coeff v := by
  exact coeff_mul_add_eq_of_natDegree_le hp hq

/-- Three-factor version of `coeff_mul_at_bounds68`. -/
theorem coeff_mul_mul_at_bounds68 (p q r : k[X]) (u v w : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hr : r.natDegree ≤ w) :
    (p * q * r).coeff (u + v + w) =
      p.coeff u * q.coeff v * r.coeff w := by
  have hpq : (p * q).natDegree ≤ u + v := by
    exact natDegree_mul_le.trans (Nat.add_le_add hp hq)
  rw [coeff_mul_add_eq_of_natDegree_le hpq hr,
    coeff_mul_add_eq_of_natDegree_le hp hq]

/-- A power has the expected coefficient at an arbitrary degree bound. -/
theorem coeff_pow_at_bound68 (p : k[X]) (u m : ℕ)
    (hp : p.natDegree ≤ u) :
    (p ^ m).coeff (m * u) = p.coeff u ^ m := by
  exact coeff_pow_of_natDegree_le hp

/-- Coefficient of a derivative at an arbitrary positive degree bound. -/
theorem coeff_derivative_at_bound68 (p : k[X]) (u : ℕ) (hu : 0 < u) :
    (derivative p).coeff (u - 1) = p.coeff u * (u : k) := by
  rw [coeff_derivative]
  have hi : u - 1 + 1 = u := by omega
  rw [hi]
  have hcast : (↑(u - 1) + 1 : k) = ↑u := by exact_mod_cast hi
  rw [hcast]

/-- Top coefficient of a product with one differentiated factor at arbitrary
separate degree bounds. -/
theorem coeff_mul_derivative_at_bounds68 (p q : k[X]) (u v : ℕ)
    (hv : 0 < v) (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (p * derivative q).coeff (u + v - 1) =
      p.coeff u * q.coeff v * (v : k) := by
  have hdq : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1)
  have h := coeff_mul_add_eq_of_natDegree_le hp hdq
  rw [coeff_derivative_at_bound68 q v hv] at h
  have hi : u + v - 1 = u + (v - 1) := by omega
  rw [hi]
  simpa only [mul_assoc] using h

/-- Two undifferentiated factors and one differentiated factor. -/
theorem coeff_mul_mul_derivative_at_bounds68 (p q r : k[X])
    (u v w : ℕ) (hw : 0 < w)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hr : r.natDegree ≤ w) :
    (p * q * derivative r).coeff (u + v + w - 1) =
      p.coeff u * q.coeff v * r.coeff w * (w : k) := by
  have hpq : (p * q).natDegree ≤ u + v :=
    natDegree_mul_le.trans (Nat.add_le_add hp hq)
  have h := coeff_mul_derivative_at_bounds68 (p * q) r (u + v) w
    hw hpq hr
  rw [coeff_mul_at_bounds68 p q u v hp hq] at h
  have hi : u + v + w - 1 = (u + v) + w - 1 := by omega
  simpa only [hi, mul_assoc] using h

/-- Three undifferentiated factors and one differentiated factor. -/
theorem coeff_mul_mul_mul_derivative_at_bounds68 (p q r s : k[X])
    (u v w z : ℕ) (hz : 0 < z)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hr : r.natDegree ≤ w) (hs : s.natDegree ≤ z) :
    (p * q * r * derivative s).coeff (u + v + w + z - 1) =
      p.coeff u * q.coeff v * r.coeff w * s.coeff z * (z : k) := by
  have hpqr : (p * q * r).natDegree ≤ u + v + w := by
    have hpq : (p * q).natDegree ≤ u + v :=
      natDegree_mul_le.trans (Nat.add_le_add hp hq)
    exact natDegree_mul_le.trans (Nat.add_le_add hpq hr)
  have h := coeff_mul_derivative_at_bounds68 (p * q * r) s
    (u + v + w) z hz hpqr hs
  rw [coeff_mul_mul_at_bounds68 p q r u v w hp hq hr] at h
  have hi : u + v + w + z - 1 = (u + v + w) + z - 1 := by omega
  simpa only [hi, mul_assoc] using h

end SecondaryExtraction68
end Max11DegreeRoutes
