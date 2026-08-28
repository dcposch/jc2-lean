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

/-- Compact polynomial form of the first invariant after translating away the
even cubic core. -/
def cubicFirstIntegralFourPolynomial68
    (l beta gamma delta epsilon zeta : k)
    (A B c D e : k[X]) : k[X] :=
  (-8 / 27 : k) • B ^ 3 - (8 / 9 : k) • (A * B * c) +
    (8 / 3 : k) • (B * e) + (8 / 3 : k) • (D * c) + zeta • A +
    (2 * epsilon : k) • B + (1 / 4 * delta : k) • A ^ 2 +
    (3 * delta : k) • c + (4 * gamma : k) • D -
    (4 / 3 * gamma : k) • (A * B) + (5 * beta : k) • e +
    (5 / 6 * beta : k) • (A * c) - (5 / 12 * beta : k) • B ^ 2 +
    (5 / 72 * beta : k) • A ^ 3 + (35 / 1728 * l : k) • A ^ 4 +
    (7 / 24 * l : k) • (A ^ 2 * c) -
    (35 / 72 * l : k) • (A * B ^ 2) +
    (7 / 6 * l : k) • (A * e) + (7 / 6 * l : k) • (B * D) +
    (7 / 12 * l : k) • c ^ 2

/-- Compact polynomial form of the second invariant in the same transverse
coordinates. -/
def cubicFirstIntegralThreePolynomial68
    (l beta gamma delta epsilon zeta : k)
    (A B c D e : k[X]) : k[X] :=
  (4 / 9 : k) • (A ^ 2 * B ^ 2) - (16 / 9 : k) • (A * B * D) -
    (8 / 9 : k) • (B ^ 2 * c) + (4 / 3 : k) • D ^ 2 +
    (8 / 3 : k) • (c * e) + zeta • B + (2 * epsilon : k) • c +
    (4 * gamma : k) • e - (2 / 3 * gamma : k) • B ^ 2 +
    (3 * delta : k) • D - (3 / 2 * delta : k) • (A * B) +
    (5 / 24 * beta : k) • (A ^ 2 * B) -
    (5 / 6 * beta : k) • (A * D) -
    (5 / 6 * beta : k) • (B * c) +
    (7 / 432 * l : k) • (A ^ 3 * B) -
    (7 / 72 * l : k) • (A ^ 2 * D) -
    (7 / 12 * l : k) • (A * B * c) -
    (35 / 216 * l : k) • B ^ 3 +
    (7 / 6 * l : k) • (B * e) + (7 / 6 * l : k) • (D * c)

/-- The terms of the first one-form row that can attain secondary deficit
two.  Every omitted homogeneous term has at least three transverse factors,
and every omitted load term has lower old weight in the chamber `2g<n`. -/
def firstSecondaryCoreRowTwoPolynomial68
    (A B c D e : k[X]) : k[X] :=
  (-4 / 27 : k) •
    ((2 : k) • (A ^ 2 * B * derivative c) +
      (2 : k) • (A ^ 2 * c * derivative B) +
      A * B * c * derivative A -
      (6 : k) • (A * D * derivative c) -
      (6 : k) • (A * c * derivative D) +
      (9 : k) • (B * e * derivative A) +
      (3 : k) • (D * c * derivative A) -
      (18 : k) • (D * derivative e) -
      (18 : k) • (e * derivative D))

/-- Load-free integrated coefficients on the cubic-coordinate chart. -/
def cubicHomogeneousSPolynomial68 (A B D : k[X]) : k[X] :=
  (4 / 9 : k) • (A * B) + (4 / 3 : k) • D

def cubicHomogeneousTPolynomial68 (A B c e : k[X]) : k[X] :=
  (4 / 27 : k) • A ^ 3 + (8 / 9 : k) • (A * c) +
    (2 / 9 : k) • B ^ 2 + (4 / 3 : k) • e

def cubicHomogeneousUPolynomial68 (A B c D : k[X]) : k[X] :=
  (4 / 9 : k) • (A * D) + (4 / 9 : k) • (B * c)

def cubicHomogeneousVPolynomial68 (A B c D e : k[X]) : k[X] :=
  (1 / 81 : k) • A ^ 4 + (4 / 27 : k) • (A ^ 2 * c) -
    (4 / 27 : k) • (A * B ^ 2) + (4 / 9 : k) • (B * D) +
    (4 / 9 : k) • (A * e) + (2 / 9 : k) • c ^ 2

/-- The complementary constant-load pieces of the four integrated
coefficients in cubic coordinates. -/
def cubicLoadSPolynomial68
    (l alpha beta delta : k) (A B c : k[X]) : k[X] :=
  (35 / 72 * l : k) • A ^ 2 + (7 / 6 * l : k) • c +
    alpha • B + (5 / 6 * beta : k) • A + C delta

def cubicLoadTPolynomial68
    (l alpha beta gamma epsilon : k) (A B c D : k[X]) : k[X] :=
  (7 / 36 * l : k) • (A * B) + (7 / 6 * l : k) • D +
    (1 / 3 * alpha : k) • A ^ 2 + alpha • c +
    (5 / 6 * beta : k) • B + (2 / 3 * gamma : k) • A + C epsilon

def cubicLoadUPolynomial68
    (l alpha beta gamma delta zeta : k)
    (A B c D e : k[X]) : k[X] :=
  (35 / 432 * l : k) • A ^ 3 + (7 / 12 * l : k) • (A * c) +
    (7 / 72 * l : k) • B ^ 2 + (7 / 6 * l : k) • e +
    alpha • D + (5 / 24 * beta : k) • A ^ 2 +
    (5 / 6 * beta : k) • c + (2 / 3 * gamma : k) • B +
    (1 / 2 * delta : k) • A + C zeta

def cubicLoadVPolynomial68
    (l alpha beta gamma delta epsilon eta : k)
    (A B c D e : k[X]) : k[X] :=
  (-7 / 432 * l : k) • (A ^ 2 * B) +
    (7 / 36 * l : k) • (A * D) + (7 / 36 * l : k) • (B * c) +
    (1 / 27 * alpha : k) • A ^ 3 +
    (1 / 3 * alpha : k) • (A * c) + alpha • e -
    (5 / 36 * beta : k) • (A * B) + (5 / 6 * beta : k) • D +
    (1 / 9 * gamma : k) • A ^ 2 + (2 / 3 * gamma : k) • c +
    (1 / 2 * delta : k) • B + (1 / 3 * epsilon : k) • A + C eta

/-- Exact decomposition of all four integrated coefficients into their
load-free cubic part and lower-weight load part. -/
structure CubicIntegratedCoordinates68
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) : Prop where
  s_eq : integratedSPolynomial68 l alpha beta delta A B
      ((1 / 3 : k) • A ^ 2 + c) D =
    cubicHomogeneousSPolynomial68 A B D +
      cubicLoadSPolynomial68 l alpha beta delta A B c
  t_eq : integratedTPolynomial68 l alpha beta gamma epsilon A B
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
    cubicHomogeneousTPolynomial68 A B c e +
      cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  u_eq : integratedUPolynomial68 l alpha beta gamma delta zeta A B
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
    cubicHomogeneousUPolynomial68 A B c D +
      cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  v_eq : integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
    cubicHomogeneousVPolynomial68 A B c D e +
      cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta A B c D e

set_option maxHeartbeats 4000000 in
theorem integratedPolynomial68_cubicCoordinates
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    CubicIntegratedCoordinates68 l alpha beta gamma delta epsilon zeta eta
      A B c D e := by
  constructor <;>
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k)) <;>
    simp only [integratedSPolynomial68, integratedTPolynomial68,
      integratedUPolynomial68, integratedVPolynomial68,
      cubicHomogeneousSPolynomial68, cubicHomogeneousTPolynomial68,
      cubicHomogeneousUPolynomial68, cubicHomogeneousVPolynomial68,
      cubicLoadSPolynomial68, cubicLoadTPolynomial68,
      cubicLoadUPolynomial68, cubicLoadVPolynomial68,
      Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      RatFunc.algebraMap_C] <;>
    simp only [map_neg, map_div₀, map_ofNat, map_one] <;>
    ring

/-- Exact load-free first one-form after the cubic translation. -/
def cubicHomogeneousRowTwoPolynomial68 (A B c D e : k[X]) : k[X] :=
  lowerRowTwoPolynomial68
    (cubicHomogeneousSPolynomial68 A B D)
    (cubicHomogeneousTPolynomial68 A B c e)
    (cubicHomogeneousUPolynomial68 A B c D)
    (cubicHomogeneousVPolynomial68 A B c D e)
    B ((1 / 3 : k) • A ^ 2 + c) D
    ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)

/-- Contribution of the constant-load pieces to the first one-form row. -/
def cubicLoadRowTwoPolynomial68
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) : k[X] :=
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Sl := cubicLoadSPolynomial68 l alpha beta delta A B c
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
    (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
    (2 : k) • (C0 * derivative Ul) - D * derivative Tl

/-- Linearity of the first one-form row under the homogeneous/load split. -/
theorem cubicRowTwoPolynomial68_split
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    lowerRowTwoPolynomial68
      (cubicHomogeneousSPolynomial68 A B D +
        cubicLoadSPolynomial68 l alpha beta delta A B c)
      (cubicHomogeneousTPolynomial68 A B c e +
        cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D)
      (cubicHomogeneousUPolynomial68 A B c D +
        cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e)
      (cubicHomogeneousVPolynomial68 A B c D e +
        cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta A B c D e)
      B ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
    cubicHomogeneousRowTwoPolynomial68 A B c D e +
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c D e := by
  simp only [cubicHomogeneousRowTwoPolynomial68,
    cubicLoadRowTwoPolynomial68, lowerRowTwoPolynomial68, derivative_add,
    Polynomial.smul_eq_C_mul]
  ring

/-- Fully expanded load-free row, grouped before degree extraction. -/
def cubicHomogeneousRowTwoExpandedPolynomial68
    (A B c D e : k[X]) : k[X] :=
  (-4 / 27 : k) •
    ((2 : k) • (A ^ 2 * B * derivative c) +
      (2 : k) • (A ^ 2 * c * derivative B) +
      A * B * c * derivative A -
      (6 : k) • (A * B ^ 2 * derivative B) -
      (6 : k) • (A * D * derivative c) -
      (6 : k) • (A * c * derivative D) -
      (3 : k) • (B ^ 3 * derivative A) +
      (9 : k) • (B * e * derivative A) +
      (3 : k) • (D * c * derivative A) +
      (6 : k) • (B ^ 2 * derivative D) +
      (12 : k) • (B * D * derivative B) +
      (12 : k) • (B * c * derivative c) +
      (6 : k) • (c ^ 2 * derivative B) -
      (18 : k) • (D * derivative e) -
      (18 : k) • (e * derivative D))

/-- The terms of secondary deficit three in the load-free first row. -/
def cubicRemainderRowTwoPolynomial68 (A B c D : k[X]) : k[X] :=
  (-4 / 27 : k) •
    (-(6 : k) • (A * B ^ 2 * derivative B) -
      (3 : k) • (B ^ 3 * derivative A) +
      (6 : k) • (B ^ 2 * derivative D) +
      (12 : k) • (B * D * derivative B) +
      (12 : k) • (B * c * derivative c) +
      (6 : k) • (c ^ 2 * derivative B))

theorem cubicHomogeneousRowTwoExpandedPolynomial68_split
    (A B c D e : k[X]) :
    cubicHomogeneousRowTwoExpandedPolynomial68 A B c D e =
      firstSecondaryCoreRowTwoPolynomial68 A B c D e +
        cubicRemainderRowTwoPolynomial68 A B c D := by
  simp only [cubicHomogeneousRowTwoExpandedPolynomial68,
    firstSecondaryCoreRowTwoPolynomial68, cubicRemainderRowTwoPolynomial68]
  module

set_option maxHeartbeats 4000000 in
theorem cubicHomogeneousRowTwoPolynomial68_eq_expanded
    (A B c D e : k[X]) :
    cubicHomogeneousRowTwoPolynomial68 A B c D e =
      cubicHomogeneousRowTwoExpandedPolynomial68 A B c D e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicHomogeneousRowTwoPolynomial68,
    cubicHomogeneousRowTwoExpandedPolynomial68,
    cubicHomogeneousSPolynomial68, cubicHomogeneousTPolynomial68,
    cubicHomogeneousUPolynomial68, cubicHomogeneousVPolynomial68,
    lowerRowTwoPolynomial68, derivative_add, derivative_sub,
    derivative_smul, derivative_mul, derivative_pow, derivative_C,
    Polynomial.C_eq_natCast,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_zero, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 2000000 in
theorem firstIntegralFourPolynomial68_cubicCoordinates
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X]) :
    firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta A B
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
        cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
          A B c D e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  rw [algebraMap_firstIntegralFourPolynomial68]
  simp only [map_add, Polynomial.smul_eq_C_mul, map_mul, map_pow,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_one]
  have hC : (1 / 3 : RatFunc k) *
        (algebraMap k[X] (RatFunc k) A) ^ 2 +
        algebraMap k[X] (RatFunc k) c =
      (algebraMap k[X] (RatFunc k) A) ^ 2 / 3 +
        algebraMap k[X] (RatFunc k) c := by ring
  have hE : (1 / 27 : RatFunc k) *
          (algebraMap k[X] (RatFunc k) A) ^ 3 +
        (1 / 3 : RatFunc k) *
          (algebraMap k[X] (RatFunc k) A *
            algebraMap k[X] (RatFunc k) c) +
        algebraMap k[X] (RatFunc k) e =
      (algebraMap k[X] (RatFunc k) A) ^ 3 / 27 +
        (algebraMap k[X] (RatFunc k) A *
          algebraMap k[X] (RatFunc k) c) / 3 +
        algebraMap k[X] (RatFunc k) e := by ring
  rw [hC, hE]
  rw [firstIntegralFour68_cubicCoordinates]
  simp only [cubicFirstIntegralFourPolynomial68, cubicFirstIntegralFour68,
    map_add, map_sub, Polynomial.smul_eq_C_mul, map_mul, map_pow,
    RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 2000000 in
theorem firstIntegralThreePolynomial68_cubicCoordinates
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X]) :
    firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta A B
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
        cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
          A B c D e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  rw [algebraMap_firstIntegralThreePolynomial68]
  simp only [map_add, Polynomial.smul_eq_C_mul, map_mul, map_pow,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_one]
  have hC : (1 / 3 : RatFunc k) *
        (algebraMap k[X] (RatFunc k) A) ^ 2 +
        algebraMap k[X] (RatFunc k) c =
      (algebraMap k[X] (RatFunc k) A) ^ 2 / 3 +
        algebraMap k[X] (RatFunc k) c := by ring
  have hE : (1 / 27 : RatFunc k) *
          (algebraMap k[X] (RatFunc k) A) ^ 3 +
        (1 / 3 : RatFunc k) *
          (algebraMap k[X] (RatFunc k) A *
            algebraMap k[X] (RatFunc k) c) +
        algebraMap k[X] (RatFunc k) e =
      (algebraMap k[X] (RatFunc k) A) ^ 3 / 27 +
        (algebraMap k[X] (RatFunc k) A *
          algebraMap k[X] (RatFunc k) c) / 3 +
        algebraMap k[X] (RatFunc k) e := by ring
  rw [hC, hE]
  rw [firstIntegralThree68_cubicCoordinates]
  simp only [cubicFirstIntegralThreePolynomial68,
    cubicFirstIntegralThree68, map_add, map_sub,
    Polynomial.smul_eq_C_mul, map_mul, map_pow, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 2000000 in
/-- In the first chamber `2g<n`, the first invariant contributes exactly the
first abstract secondary-face equation. -/
theorem cubicFirstIntegralFourPolynomial68_secondaryCoeff
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        A B c D e).coeff (9 * n - 2 * g) =
      (-8 / 9 : k) * firstSecondaryFour68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have lower (p : k[X]) (hp : p.natDegree < 9 * n - 2 * g) :
      p.coeff (9 * n - 2 * g) = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hABC : (A * B * c).coeff (9 * n - 2 * g) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) := by
    have h := coeff_mul_mul_at_bounds68 A B c (2 * n)
      (3 * n - g) (4 * n - g) hA hB hc
    have hi : 2 * n + (3 * n - g) + (4 * n - g) =
        9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBe : (B * e).coeff (9 * n - 2 * g) =
      B.coeff (3 * n - g) * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - g) hB he
    have hi : (3 * n - g) + (6 * n - g) = 9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hDc : (D * c).coeff (9 * n - 2 * g) =
      D.coeff (5 * n - g) * c.coeff (4 * n - g) := by
    have h := coeff_mul_at_bounds68 D c (5 * n - g) (4 * n - g) hD hc
    have hi : (5 * n - g) + (4 * n - g) = 9 * n - 2 * g := by omega
    simpa only [hi] using h
  have hB3 : (B ^ 3).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hAz : A.coeff (9 * n - 2 * g) = 0 :=
    lower _ (by omega)
  have hBz : B.coeff (9 * n - 2 * g) = 0 :=
    lower _ (by omega)
  have hA2 : (A ^ 2).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hcz : c.coeff (9 * n - 2 * g) = 0 :=
    lower _ (by omega)
  have hDz : D.coeff (9 * n - 2 * g) = 0 :=
    lower _ (by omega)
  have hAB : (A * B).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hez : e.coeff (9 * n - 2 * g) = 0 :=
    lower _ (by omega)
  have hAc : (A * c).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hB2 : (B ^ 2).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hA3 : (A ^ 3).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hA4 : (A ^ 4).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hA2c : (A ^ 2 * c).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hAB2 : (A * B ^ 2).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hAe : (A * e).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hBD : (B * D).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hc2 : (c ^ 2).coeff (9 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  simp only [cubicFirstIntegralFourPolynomial68, coeff_add, coeff_sub,
    coeff_smul, hABC, hBe, hDc, hB3, hAz, hBz, hA2, hcz, hDz,
    hAB, hez, hAc, hB2, hA3, hA4, hA2c, hAB2, hAe, hBD, hc2,
    smul_eq_mul, mul_zero, add_zero, sub_zero]
  simp only [firstSecondaryFour68]
  ring

set_option maxHeartbeats 2000000 in
/-- In the first chamber `2g<n`, the second invariant contributes exactly the
second abstract secondary-face equation. -/
theorem cubicFirstIntegralThreePolynomial68_secondaryCoeff
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        A B c D e).coeff (10 * n - 2 * g) =
      (4 / 9 : k) * firstSecondaryThree68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have lower (p : k[X]) (hp : p.natDegree < 10 * n - 2 * g) :
      p.coeff (10 * n - 2 * g) = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hA2coeff : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have hB2coeff : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hA2B2 : (A ^ 2 * B ^ 2).coeff (10 * n - 2 * g) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_mul_at_bounds68 (A ^ 2) (B ^ 2) (4 * n)
      (6 * n - 2 * g) hA2deg hB2deg
    have hi : 4 * n + (6 * n - 2 * g) = 10 * n - 2 * g := by omega
    rw [hi, hA2coeff, hB2coeff] at h
    exact h
  have hABD : (A * B * D).coeff (10 * n - 2 * g) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        D.coeff (5 * n - g) := by
    have h := coeff_mul_mul_at_bounds68 A B D (2 * n)
      (3 * n - g) (5 * n - g) hA hB hD
    have hi : 2 * n + (3 * n - g) + (5 * n - g) =
        10 * n - 2 * g := by omega
    simpa only [hi] using h
  have hD2 : (D ^ 2).coeff (10 * n - 2 * g) =
      D.coeff (5 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 D (5 * n - g) 2 hD
    have hi : 2 * (5 * n - g) = 10 * n - 2 * g := by omega
    simpa only [hi] using h
  have hce : (c * e).coeff (10 * n - 2 * g) =
      c.coeff (4 * n - g) * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - g) hc he
    have hi : (4 * n - g) + (6 * n - g) = 10 * n - 2 * g := by omega
    simpa only [hi] using h
  have hB2c : (B ^ 2 * c).coeff (10 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hBz : B.coeff (10 * n - 2 * g) = 0 := lower _ (by omega)
  have hcz : c.coeff (10 * n - 2 * g) = 0 := lower _ (by omega)
  have hez : e.coeff (10 * n - 2 * g) = 0 := lower _ (by omega)
  have hB2z : (B ^ 2).coeff (10 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hDz : D.coeff (10 * n - 2 * g) = 0 := lower _ (by omega)
  have hAB : (A * B).coeff (10 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hA2B : (A ^ 2 * B).coeff (10 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hAD : (A * D).coeff (10 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hBc : (B * c).coeff (10 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hA3B : (A ^ 3 * B).coeff (10 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hA2D : (A ^ 2 * D).coeff (10 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hABc : (A * B * c).coeff (10 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hB3 : (B ^ 3).coeff (10 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hBe : (B * e).coeff (10 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  have hDc : (D * c).coeff (10 * n - 2 * g) = 0 :=
    lower _ (by compute_degree; omega)
  simp only [cubicFirstIntegralThreePolynomial68, coeff_add, coeff_sub,
    coeff_smul, hA2B2, hABD, hB2c, hD2, hce, hBz, hcz, hez, hB2z,
    hDz, hAB, hA2B, hAD, hBc, hA3B, hA2D, hABc, hB3, hBe, hDc,
    smul_eq_mul, mul_zero, add_zero, sub_zero]
  simp only [firstSecondaryThree68]
  ring

set_option maxHeartbeats 2000000 in
/-- The deficit-two core of the first one-form row has exactly the third
abstract secondary-face coefficient. -/
theorem firstSecondaryCoreRowTwoPolynomial68_coeff
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (firstSecondaryCoreRowTwoPolynomial68 A B c D e).coeff
        (11 * n - 2 * g - 1) =
      (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hA2coeff : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have h1 : (A ^ 2 * B * derivative c).coeff
      (11 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) * ((4 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B c
      (4 * n) (3 * n - g) (4 * n - g) (by omega) hA2deg hB hc
    have hi : 4 * n + (3 * n - g) + (4 * n - g) - 1 =
        11 * n - 2 * g - 1 := by omega
    rw [hi, hA2coeff] at h
    exact h
  have h2 : (A ^ 2 * c * derivative B).coeff
      (11 * n - 2 * g - 1) =
      A.coeff (2 * n) ^ 2 * c.coeff (4 * n - g) *
        B.coeff (3 * n - g) * ((3 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) c B
      (4 * n) (4 * n - g) (3 * n - g) (by omega) hA2deg hc hB
    have hi : 4 * n + (4 * n - g) + (3 * n - g) - 1 =
        11 * n - 2 * g - 1 := by omega
    rw [hi, hA2coeff] at h
    exact h
  have h3 : (A * B * c * derivative A).coeff
      (11 * n - 2 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 A B c A
      (2 * n) (3 * n - g) (4 * n - g) (2 * n) (by omega)
      hA hB hc hA
    have hi : 2 * n + (3 * n - g) + (4 * n - g) + 2 * n - 1 =
        11 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h4 : (A * D * derivative c).coeff (11 * n - 2 * g - 1) =
      A.coeff (2 * n) * D.coeff (5 * n - g) *
        c.coeff (4 * n - g) * ((4 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A D c
      (2 * n) (5 * n - g) (4 * n - g) (by omega) hA hD hc
    have hi : 2 * n + (5 * n - g) + (4 * n - g) - 1 =
        11 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h5 : (A * c * derivative D).coeff (11 * n - 2 * g - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        D.coeff (5 * n - g) * ((5 * n - g : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A c D
      (2 * n) (4 * n - g) (5 * n - g) (by omega) hA hc hD
    have hi : 2 * n + (4 * n - g) + (5 * n - g) - 1 =
        11 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h6 : (B * e * derivative A).coeff (11 * n - 2 * g - 1) =
      B.coeff (3 * n - g) * e.coeff (6 * n - g) *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 B e A
      (3 * n - g) (6 * n - g) (2 * n) (by omega) hB he hA
    have hi : (3 * n - g) + (6 * n - g) + 2 * n - 1 =
        11 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h7 : (D * c * derivative A).coeff (11 * n - 2 * g - 1) =
      D.coeff (5 * n - g) * c.coeff (4 * n - g) *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 D c A
      (5 * n - g) (4 * n - g) (2 * n) (by omega) hD hc hA
    have hi : (5 * n - g) + (4 * n - g) + 2 * n - 1 =
        11 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h8 : (D * derivative e).coeff (11 * n - 2 * g - 1) =
      D.coeff (5 * n - g) * e.coeff (6 * n - g) *
        ((6 * n - g : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 D e
      (5 * n - g) (6 * n - g) (by omega) hD he
    have hi : (5 * n - g) + (6 * n - g) - 1 =
        11 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  have h9 : (e * derivative D).coeff (11 * n - 2 * g - 1) =
      e.coeff (6 * n - g) * D.coeff (5 * n - g) *
        ((5 * n - g : ℕ) : k) := by
    have h := coeff_mul_derivative_at_bounds68 e D
      (6 * n - g) (5 * n - g) (by omega) he hD
    have hi : (6 * n - g) + (5 * n - g) - 1 =
        11 * n - 2 * g - 1 := by omega
    simpa only [hi] using h
  simp only [firstSecondaryCoreRowTwoPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2, h3, h4, h5, h6, h7, h8, h9, smul_eq_mul]
  have hg3 : g ≤ 3 * n := by omega
  have hg4 : g ≤ 4 * n := by omega
  have hg5 : g ≤ 5 * n := by omega
  have hg6 : g ≤ 6 * n := by omega
  have hcast3 : (((3 * n - g : ℕ) : k)) = (n : k) * 3 - (g : k) := by
    rw [Nat.cast_sub hg3]
    push_cast
    ring
  have hcast4 : (((4 * n - g : ℕ) : k)) = (n : k) * 4 - (g : k) := by
    rw [Nat.cast_sub hg4]
    push_cast
    ring
  have hcast5 : (((5 * n - g : ℕ) : k)) = (n : k) * 5 - (g : k) := by
    rw [Nat.cast_sub hg5]
    push_cast
    ring
  have hcast6 : (((6 * n - g : ℕ) : k)) = (n : k) * 6 - (g : k) := by
    rw [Nat.cast_sub hg6]
    push_cast
    ring
  rw [hcast3, hcast4, hcast5, hcast6]
  push_cast
  simp only [firstSecondaryTwo68]
  ring

set_option maxHeartbeats 2000000 in
/-- The complete load-free first one-form has the same deficit-two
coefficient as its core; its remaining monomials have deficit three. -/
theorem cubicHomogeneousRowTwoPolynomial68_secondaryCoeff
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicHomogeneousRowTwoPolynomial68 A B c D e).coeff
        (11 * n - 2 * g - 1) =
      (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hrem : (cubicRemainderRowTwoPolynomial68 A B c D).natDegree <
      11 * n - 2 * g - 1 := by
    simp only [cubicRemainderRowTwoPolynomial68]
    compute_degree
    omega
  rw [cubicHomogeneousRowTwoPolynomial68_eq_expanded,
    cubicHomogeneousRowTwoExpandedPolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrem, add_zero]
  exact firstSecondaryCoreRowTwoPolynomial68_coeff A B c D e n g
    hn hg hsmall hA hB hc hD he

set_option maxHeartbeats 2000000 in
/-- The constant-load pieces lie strictly below the homogeneous cubic weights
needed by the first secondary row. -/
theorem cubicLoadPolynomials68_degreeBounds
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadSPolynomial68 l alpha beta delta A B c).natDegree ≤ 4 * n ∧
    (cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D).natDegree ≤
      5 * n - g ∧
    (cubicLoadUPolynomial68 l alpha beta gamma delta zeta
      A B c D e).natDegree ≤ 6 * n ∧
    (cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
      A B c D e).natDegree ≤ 7 * n - g := by
  simp only [cubicLoadSPolynomial68, cubicLoadTPolynomial68,
    cubicLoadUPolynomial68, cubicLoadVPolynomial68]
  constructor
  · compute_degree
    omega
  constructor
  · compute_degree
    omega
  constructor <;> compute_degree <;> omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoPolynomial68_degree_lt
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 11 * n - 2 * g - 1 := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Sl := cubicLoadSPolynomial68 l alpha beta delta A B c
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall hA hB hc hD he
  have hSl : Sl.natDegree ≤ 4 * n := by simpa only [Sl] using hloads.1
  have hTl : Tl.natDegree ≤ 5 * n - g := by
    simpa only [Tl] using hloads.2.1
  have hUl : Ul.natDegree ≤ 6 * n := by
    simpa only [Ul] using hloads.2.2.1
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]
    compute_degree
    omega
  have hUlC : (Ul * derivative C0).natDegree < 11 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hTlD : (Tl * derivative D).natDegree < 11 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hSlE : (Sl * derivative E).natDegree < 11 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hBVl : (B * derivative Vl).natDegree < 11 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hC0Ul : (C0 * derivative Ul).natDegree < 11 * n - 2 * g - 1 := by
    compute_degree
    omega
  have hDTl : (D * derivative Tl).natDegree < 11 * n - 2 * g - 1 := by
    compute_degree
    omega
  change (Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
    (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
    (2 : k) • (C0 * derivative Ul) - D * derivative Tl).natDegree < _
  compute_degree
  omega

set_option maxHeartbeats 3000000 in
/-- The literal integrated first one-form supplies `F₂` at its first
secondary coefficient. -/
theorem integratedLowerRowTwoPolynomial68_secondaryCoeff
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta A B
        ((1 / 3 : k) • A ^ 2 + c) D)
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      B ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (11 * n - 2 * g - 1) =
      (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.s_eq, hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowTwoPolynomial68_split, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowTwoPolynomial68_degree_lt
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hsmall hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowTwoPolynomial68_secondaryCoeff A B c D e n g
    hn hg hsmall hA hB hc hD he

set_option maxHeartbeats 2000000 in
/-- Constant values of the two genuine polynomial invariants force the first
two equations of the abstract secondary face. -/
theorem polynomialSecondaryInvariantEquations68
    (l beta gamma delta epsilon zeta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hI4 : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i4)
    (hI3 : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i3) :
    firstSecondaryFour68 (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) = 0 ∧
      firstSecondaryThree68 (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) = 0 := by
  have ht4 : 9 * n - 2 * g ≠ 0 := by omega
  have ht3 : 10 * n - 2 * g ≠ 0 := by omega
  have hfour := congrArg (fun p : k[X] => p.coeff (9 * n - 2 * g)) hI4
  rw [hC0, hE0, firstIntegralFourPolynomial68_cubicCoordinates,
    cubicFirstIntegralFourPolynomial68_secondaryCoeff
      l beta gamma delta epsilon zeta A B c D e n g hn hg hsmall
      hA hB hc hD he] at hfour
  simp only [coeff_C, if_neg ht4] at hfour
  have hthree := congrArg (fun p : k[X] => p.coeff (10 * n - 2 * g)) hI3
  rw [hC0, hE0, firstIntegralThreePolynomial68_cubicCoordinates,
    cubicFirstIntegralThreePolynomial68_secondaryCoeff
      l beta gamma delta epsilon zeta A B c D e n g hn hg hsmall
      hA hB hc hD he] at hthree
  simp only [coeff_C, if_neg ht3] at hthree
  constructor
  · exact (mul_eq_zero.mp hfour).resolve_left (by norm_num)
  · exact (mul_eq_zero.mp hthree).resolve_left (by norm_num)

end SecondaryExtraction68

#print axioms coeff_mul_at_bounds68
#print axioms coeff_mul_mul_at_bounds68
#print axioms coeff_pow_at_bound68
#print axioms firstIntegralFourPolynomial68_cubicCoordinates
#print axioms firstIntegralThreePolynomial68_cubicCoordinates
#print axioms cubicFirstIntegralFourPolynomial68_secondaryCoeff
#print axioms cubicFirstIntegralThreePolynomial68_secondaryCoeff
#print axioms firstSecondaryCoreRowTwoPolynomial68_coeff
#print axioms cubicHomogeneousRowTwoPolynomial68_secondaryCoeff
#print axioms cubicLoadPolynomials68_degreeBounds
#print axioms cubicLoadRowTwoPolynomial68_degree_lt
#print axioms integratedLowerRowTwoPolynomial68_secondaryCoeff
#print axioms polynomialSecondaryInvariantEquations68

end Max11DegreeRoutes
