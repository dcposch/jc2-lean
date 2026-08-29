import LowScale68SecondaryFirstLoadWallCore

/-! # Core-plus-rest split of the first loaded `(6,8)` wall loads

The already checked Jacobian cores
`cubicLoadRowTwoLCorePolynomial68` and `cubicLoadRowZeroLCorePolynomial68`
are the unique `l A^5` / `l A^6` combinations that meet the wall indices
`10n-1` and `12n-1`.  This module identifies the *full* load polynomials
with those cores plus an explicit remainder of strictly lower degree.

The algebraic split is a ring/module identity (no degree cancellation).
Each leftover summand is then bounded term-by-term against the wall.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FirstLoadWallRemainder68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Load cores and complementary remainders -/

/-- Pure `l A^2` summand of `cubicLoadSPolynomial68`. -/
def cubicLoadSCorePolynomial68 (l : k) (A : k[X]) : k[X] :=
  (35 / 72 * l : k) • A ^ 2

/-- Complementary part of `cubicLoadSPolynomial68`. -/
def cubicLoadSRestPolynomial68
    (l alpha beta delta : k) (A B c : k[X]) : k[X] :=
  (7 / 6 * l : k) • c + alpha • B + (5 / 6 * beta : k) • A + C delta

/-- Pure `l A^3` summand of `cubicLoadUPolynomial68`. -/
def cubicLoadUCorePolynomial68 (l : k) (A : k[X]) : k[X] :=
  (35 / 432 * l : k) • A ^ 3

/-- Complementary part of `cubicLoadUPolynomial68`. -/
def cubicLoadURestPolynomial68
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X]) : k[X] :=
  (7 / 12 * l : k) • (A * c) +
    (7 / 72 * l : k) • B ^ 2 + (7 / 6 * l : k) • e +
    alpha • D + (5 / 24 * beta : k) • A ^ 2 +
    (5 / 6 * beta : k) • c + (2 / 3 * gamma : k) • B +
    (1 / 2 * delta : k) • A + C zeta

/-- Non-cubic part of `E`. -/
def cubicERestPolynomial68 (A c e : k[X]) : k[X] :=
  (1 / 3 : k) • (A * c) + e

theorem cubicLoadSPolynomial68_eq_core_add_rest
    (l alpha beta delta : k) (A B c : k[X]) :
    cubicLoadSPolynomial68 l alpha beta delta A B c =
      cubicLoadSCorePolynomial68 l A +
        cubicLoadSRestPolynomial68 l alpha beta delta A B c := by
  simp only [cubicLoadSPolynomial68, cubicLoadSCorePolynomial68,
    cubicLoadSRestPolynomial68, Polynomial.smul_eq_C_mul]
  ring

theorem cubicLoadUPolynomial68_eq_core_add_rest
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X]) :
    cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e =
      cubicLoadUCorePolynomial68 l A +
        cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
          A B c D e := by
  simp only [cubicLoadUPolynomial68, cubicLoadUCorePolynomial68,
    cubicLoadURestPolynomial68, Polynomial.smul_eq_C_mul]
  ring

theorem cubicLoadRowTwoLCorePolynomial68_eq_pieces (l : k) (A : k[X]) :
    cubicLoadRowTwoLCorePolynomial68 l A =
      cubicLoadUCorePolynomial68 l A *
          derivative ((1 / 3 : k) • A ^ 2) +
        (3 : k) • (cubicLoadSCorePolynomial68 l A *
          derivative ((1 / 27 : k) • A ^ 3)) -
        (2 : k) • (((1 / 3 : k) • A ^ 2) *
          derivative (cubicLoadUCorePolynomial68 l A)) := rfl

theorem cubicLoadRowZeroLCorePolynomial68_eq_pieces (l : k) (A : k[X]) :
    cubicLoadRowZeroLCorePolynomial68 l A =
      cubicLoadUCorePolynomial68 l A *
        derivative ((1 / 27 : k) • A ^ 3) := rfl

/-! ## Bilinear core-plus-rest identities

These are ring identities: they do not use degree bounds.  The leftover
summands are written in distributed form, so later degree comparisons never
see a `10n-1` or `12n-1` pair that would have to cancel. -/

set_option maxHeartbeats 2000000 in
theorem jacobianRowTwo_eq_core_add_rest
    (Ulc Ulr C0c Cr Slc Slr Ec Er T V B D : k[X]) :
    (Ulc + Ulr) * derivative (C0c + Cr) +
      (2 : k) • (T * derivative D) +
      (3 : k) • ((Slc + Slr) * derivative (Ec + Er)) -
      (3 : k) • (B * derivative V) -
      (2 : k) • ((C0c + Cr) * derivative (Ulc + Ulr)) -
      D * derivative T =
    (Ulc * derivative C0c + (3 : k) • (Slc * derivative Ec) -
      (2 : k) • (C0c * derivative Ulc)) +
    (Ulc * derivative Cr + Ulr * derivative (C0c + Cr) +
      (2 : k) • (T * derivative D) +
      (3 : k) • (Slc * derivative Er) +
      (3 : k) • (Slr * derivative (Ec + Er)) -
      (3 : k) • (B * derivative V) -
      (2 : k) • (C0c * derivative Ulr) -
      (2 : k) • (Cr * derivative (Ulc + Ulr)) -
      D * derivative T) := by
  simp only [derivative_add, mul_add, add_mul, Polynomial.smul_eq_C_mul]
  ring

set_option maxHeartbeats 1000000 in
theorem jacobianRowZero_eq_core_add_rest
    (Ulc Ulr Ec Er V D : k[X]) :
    (Ulc + Ulr) * derivative (Ec + Er) - D * derivative V =
      Ulc * derivative Ec +
        (Ulc * derivative Er + Ulr * derivative (Ec + Er) -
          D * derivative V) := by
  simp only [derivative_add, mul_add, add_mul]
  ring

/-- Explicit leftover of the first one-form load after removing the
`l A^5` Jacobian core. -/
def cubicLoadRowTwoRestPolynomial68
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) : k[X] :=
  let Ulc := cubicLoadUCorePolynomial68 l A
  let Ulr := cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
    A B c D e
  let Ul := Ulc + Ulr
  let C0c := (1 / 3 : k) • A ^ 2
  let C0 := C0c + c
  let Slc := cubicLoadSCorePolynomial68 l A
  let Slr := cubicLoadSRestPolynomial68 l alpha beta delta A B c
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := cubicERestPolynomial68 A c e
  let E := Ec + Er
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  Ulc * derivative c + Ulr * derivative C0 +
    (2 : k) • (Tl * derivative D) +
    (3 : k) • (Slc * derivative Er) +
    (3 : k) • (Slr * derivative E) -
    (3 : k) • (B * derivative Vl) -
    (2 : k) • (C0c * derivative Ulr) -
    (2 : k) • (c * derivative Ul) -
    D * derivative Tl

/-- Explicit leftover of the terminal load after removing the `l A^6`
Jacobian core. -/
def cubicLoadRowZeroRestPolynomial68
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) : k[X] :=
  let Ulc := cubicLoadUCorePolynomial68 l A
  let Ulr := cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
    A B c D e
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := cubicERestPolynomial68 A c e
  let E := Ec + Er
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  Ulc * derivative Er + Ulr * derivative E - D * derivative Vl

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoPolynomial68_eq_splitPieces
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e =
      (cubicLoadUCorePolynomial68 l A +
          cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
            A B c D e) *
        derivative ((1 / 3 : k) • A ^ 2 + c) +
      (2 : k) • (cubicLoadTPolynomial68 l alpha beta gamma epsilon
        A B c D * derivative D) +
      (3 : k) • ((cubicLoadSCorePolynomial68 l A +
          cubicLoadSRestPolynomial68 l alpha beta delta A B c) *
        derivative ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)) -
      (3 : k) • (B * derivative (cubicLoadVPolynomial68 l alpha beta gamma
        delta epsilon eta A B c D e)) -
      (2 : k) • (((1 / 3 : k) • A ^ 2 + c) *
        derivative (cubicLoadUCorePolynomial68 l A +
          cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
            A B c D e)) -
      D * derivative (cubicLoadTPolynomial68 l alpha beta gamma epsilon
        A B c D) := by
  rw [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68_eq_core_add_rest,
    cubicLoadUPolynomial68_eq_core_add_rest]

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoRestPolynomial68_eq_splitPieces
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowTwoRestPolynomial68 l alpha beta gamma delta epsilon
      zeta eta A B c D e =
      cubicLoadUCorePolynomial68 l A * derivative c +
        cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
          A B c D e * derivative ((1 / 3 : k) • A ^ 2 + c) +
        (2 : k) • (cubicLoadTPolynomial68 l alpha beta gamma epsilon
          A B c D * derivative D) +
        (3 : k) • (cubicLoadSCorePolynomial68 l A *
          derivative (cubicERestPolynomial68 A c e)) +
        (3 : k) • (cubicLoadSRestPolynomial68 l alpha beta delta A B c *
          derivative ((1 / 27 : k) • A ^ 3 + cubicERestPolynomial68 A c e)) -
        (3 : k) • (B * derivative (cubicLoadVPolynomial68 l alpha beta gamma
          delta epsilon eta A B c D e)) -
        (2 : k) • (((1 / 3 : k) • A ^ 2) *
          derivative (cubicLoadURestPolynomial68 l alpha beta gamma delta
            zeta A B c D e)) -
        (2 : k) • (c * derivative (cubicLoadUCorePolynomial68 l A +
          cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
            A B c D e)) -
        D * derivative (cubicLoadTPolynomial68 l alpha beta gamma epsilon
          A B c D) := by
  simp only [cubicLoadRowTwoRestPolynomial68]

set_option maxHeartbeats 3000000 in
theorem cubicLoadRowTwoPolynomial68_eq_lCore_add_rest
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e =
      cubicLoadRowTwoLCorePolynomial68 l A +
        cubicLoadRowTwoRestPolynomial68 l alpha beta gamma delta epsilon
          zeta eta A B c D e := by
  have hE : (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e =
      (1 / 27 : k) • A ^ 3 + cubicERestPolynomial68 A c e := by
    simp only [cubicERestPolynomial68, Polynomial.smul_eq_C_mul]
    ring
  rw [cubicLoadRowTwoPolynomial68_eq_splitPieces, hE,
    jacobianRowTwo_eq_core_add_rest
      (cubicLoadUCorePolynomial68 l A)
      (cubicLoadURestPolynomial68 l alpha beta gamma delta zeta A B c D e)
      ((1 / 3 : k) • A ^ 2) c
      (cubicLoadSCorePolynomial68 l A)
      (cubicLoadSRestPolynomial68 l alpha beta delta A B c)
      ((1 / 27 : k) • A ^ 3) (cubicERestPolynomial68 A c e)
      (cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D)
      (cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
        A B c D e)
      B D,
    ← cubicLoadRowTwoLCorePolynomial68_eq_pieces,
    ← cubicLoadRowTwoRestPolynomial68_eq_splitPieces]

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowZeroPolynomial68_eq_splitPieces
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e =
      (cubicLoadUCorePolynomial68 l A +
          cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
            A B c D e) *
        derivative ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) -
      D * derivative (cubicLoadVPolynomial68 l alpha beta gamma delta
        epsilon eta A B c D e) := by
  rw [cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68_eq_core_add_rest]

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowZeroRestPolynomial68_eq_splitPieces
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowZeroRestPolynomial68 l alpha beta gamma delta epsilon
      zeta eta A B c D e =
      cubicLoadUCorePolynomial68 l A *
          derivative (cubicERestPolynomial68 A c e) +
        cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
          A B c D e *
          derivative ((1 / 27 : k) • A ^ 3 + cubicERestPolynomial68 A c e) -
        D * derivative (cubicLoadVPolynomial68 l alpha beta gamma delta
          epsilon eta A B c D e) := by
  simp only [cubicLoadRowZeroRestPolynomial68]

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowZeroPolynomial68_eq_lCore_add_rest
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e =
      cubicLoadRowZeroLCorePolynomial68 l A +
        cubicLoadRowZeroRestPolynomial68 l alpha beta gamma delta epsilon
          zeta eta A B c D e := by
  have hE : (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e =
      (1 / 27 : k) • A ^ 3 + cubicERestPolynomial68 A c e := by
    simp only [cubicERestPolynomial68, Polynomial.smul_eq_C_mul]
    ring
  rw [cubicLoadRowZeroPolynomial68_eq_splitPieces, hE,
    jacobianRowZero_eq_core_add_rest
      (cubicLoadUCorePolynomial68 l A)
      (cubicLoadURestPolynomial68 l alpha beta gamma delta zeta A B c D e)
      ((1 / 27 : k) • A ^ 3) (cubicERestPolynomial68 A c e)
      (cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
        A B c D e)
      D,
    ← cubicLoadRowZeroLCorePolynomial68_eq_pieces,
    ← cubicLoadRowZeroRestPolynomial68_eq_splitPieces]

/-! ## Term-by-term degree bounds on the wall `2g = n`

Every leftover product is estimated from the rest-piece bounds
`≤ 4n-g` / `≤ 6n-g`.  The comparison never relies on `compute_degree`
discovering a cancellation among `10n-1` or `12n-1` summands. -/

private theorem natDegree_mul_derivative_le_add_sub68
    (p q : k[X]) (u v : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (p * derivative q).natDegree ≤ u + v - 1 := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1)
  have hsum : p.natDegree + (derivative q).natDegree ≤ u + (v - 1) :=
    Nat.add_le_add hp hd
  have hidx : u + (v - 1) = u + v - 1 := by omega
  exact natDegree_mul_le.trans (hidx ▸ hsum)

private theorem natDegree_mul_derivative_lt_of_add_sub68
    (p q : k[X]) (u v bound : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (huv : u + v - 1 < bound) :
    (p * derivative q).natDegree < bound :=
  (natDegree_mul_derivative_le_add_sub68 p q u v hv hp hq).trans_lt huv

private theorem natDegree_smul_lt68 (r : k) {p : k[X]} {n : ℕ}
    (hp : p.natDegree < n) : (r • p).natDegree < n :=
  (natDegree_smul_le r p).trans_lt hp

private theorem natDegree_add_lt68 {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p + q).natDegree < n :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem natDegree_sub_lt68 {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p - q).natDegree < n :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

set_option maxHeartbeats 2000000 in
theorem cubicLoadSRestPolynomial68_degree_le_loadWall
    (l alpha beta delta : k) (A B c : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadSRestPolynomial68 l alpha beta delta A B c).natDegree ≤
      4 * n - g := by
  simp only [cubicLoadSRestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadURestPolynomial68_degree_le_loadWall
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
      A B c D e).natDegree ≤ 6 * n - g := by
  simp only [cubicLoadURestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicERestPolynomial68_degree_le_loadWall
    (A c e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicERestPolynomial68 A c e).natDegree ≤ 6 * n - g := by
  simp only [cubicERestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadSCorePolynomial68_degree_le
    (l : k) (A : k[X]) (n : ℕ) (hA : A.natDegree ≤ 2 * n) :
    (cubicLoadSCorePolynomial68 l A).natDegree ≤ 4 * n := by
  simp only [cubicLoadSCorePolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadUCorePolynomial68_degree_le
    (l : k) (A : k[X]) (n : ℕ) (hA : A.natDegree ≤ 2 * n) :
    (cubicLoadUCorePolynomial68 l A).natDegree ≤ 6 * n := by
  simp only [cubicLoadUCorePolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowTwoRestPolynomial68_degree_lt_loadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoRestPolynomial68 l alpha beta gamma delta epsilon
      zeta eta A B c D e).natDegree < 10 * n - 1 := by
  let Ulc := cubicLoadUCorePolynomial68 l A
  let Ulr := cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
    A B c D e
  let Ul := Ulc + Ulr
  let C0c := (1 / 3 : k) • A ^ 2
  let C0 := C0c + c
  let Slc := cubicLoadSCorePolynomial68 l A
  let Slr := cubicLoadSRestPolynomial68 l alpha beta delta A B c
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := cubicERestPolynomial68 A c e
  let E := Ec + Er
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hloads := cubicLoadPolynomials68_degreeBounds_loadWall
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hwall hA hB hc hD he
  have hUlc : Ulc.natDegree ≤ 6 * n :=
    cubicLoadUCorePolynomial68_degree_le l A n hA
  have hUlr : Ulr.natDegree ≤ 6 * n - g :=
    cubicLoadURestPolynomial68_degree_le_loadWall
      l alpha beta gamma delta zeta A B c D e n g
      hn hg hwall hA hB hc hD he
  have hUl : Ul.natDegree ≤ 6 * n :=
    (natDegree_add_le Ulc Ulr).trans (max_le hUlc (hUlr.trans (by omega)))
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0, C0c]
    compute_degree
    omega
  have hSlc : Slc.natDegree ≤ 4 * n :=
    cubicLoadSCorePolynomial68_degree_le l A n hA
  have hSlr : Slr.natDegree ≤ 4 * n - g :=
    cubicLoadSRestPolynomial68_degree_le_loadWall
      l alpha beta delta A B c n g hn hg hwall hA hB hc
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g :=
    cubicERestPolynomial68_degree_le_loadWall A c e n g
      hn hg hwall hA hc he
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hTl : Tl.natDegree ≤ 5 * n - g := by
    simpa only [Tl] using hloads.2.1
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have hbound (u v : ℕ) (hv : 0 < v) (hu : u + v - 1 < 10 * n - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 10 * n - 1 :=
    fun p q hp hq =>
      natDegree_mul_derivative_lt_of_add_sub68 p q u v (10 * n - 1) hv hp hq hu
  have h1 : (Ulc * derivative c).natDegree < 10 * n - 1 :=
    hbound (6 * n) (4 * n - g) (by omega) (by omega) Ulc c hUlc hc
  have h2 : (Ulr * derivative C0).natDegree < 10 * n - 1 :=
    hbound (6 * n - g) (4 * n) (by omega) (by omega) Ulr C0 hUlr hC0
  have h3 : (Tl * derivative D).natDegree < 10 * n - 1 :=
    hbound (5 * n - g) (5 * n - g) (by omega) (by omega) Tl D hTl hD
  have h4 : (Slc * derivative Er).natDegree < 10 * n - 1 :=
    hbound (4 * n) (6 * n - g) (by omega) (by omega) Slc Er hSlc hEr
  have h5 : (Slr * derivative E).natDegree < 10 * n - 1 :=
    hbound (4 * n - g) (6 * n) (by omega) (by omega) Slr E hSlr hE
  have h6 : (B * derivative Vl).natDegree < 10 * n - 1 :=
    hbound (3 * n - g) (7 * n - g) (by omega) (by omega) B Vl hB hVl
  have h7 : (C0c * derivative Ulr).natDegree < 10 * n - 1 :=
    hbound (4 * n) (6 * n - g) (by omega) (by omega) C0c Ulr hC0c hUlr
  have h8 : (c * derivative Ul).natDegree < 10 * n - 1 :=
    hbound (4 * n - g) (6 * n) (by omega) (by omega) c Ul hc hUl
  have h9 : (D * derivative Tl).natDegree < 10 * n - 1 :=
    hbound (5 * n - g) (5 * n - g) (by omega) (by omega) D Tl hD hTl
  have h3s := natDegree_smul_lt68 (2 : k) h3
  have h4s := natDegree_smul_lt68 (3 : k) h4
  have h5s := natDegree_smul_lt68 (3 : k) h5
  have h6s := natDegree_smul_lt68 (3 : k) h6
  have h7s := natDegree_smul_lt68 (2 : k) h7
  have h8s := natDegree_smul_lt68 (2 : k) h8
  have s1 := natDegree_add_lt68 h1 h2
  have s2 := natDegree_add_lt68 s1 h3s
  have s3 := natDegree_add_lt68 s2 h4s
  have s4 := natDegree_add_lt68 s3 h5s
  have s5 := natDegree_sub_lt68 s4 h6s
  have s6 := natDegree_sub_lt68 s5 h7s
  have s7 := natDegree_sub_lt68 s6 h8s
  have s8 := natDegree_sub_lt68 s7 h9
  rw [cubicLoadRowTwoRestPolynomial68_eq_splitPieces]
  exact s8

set_option maxHeartbeats 3000000 in
theorem cubicLoadRowZeroRestPolynomial68_degree_lt_loadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowZeroRestPolynomial68 l alpha beta gamma delta epsilon
      zeta eta A B c D e).natDegree < 12 * n - 1 := by
  let Ulc := cubicLoadUCorePolynomial68 l A
  let Ulr := cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
    A B c D e
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := cubicERestPolynomial68 A c e
  let E := Ec + Er
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hloads := cubicLoadPolynomials68_degreeBounds_loadWall
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hwall hA hB hc hD he
  have hUlc : Ulc.natDegree ≤ 6 * n :=
    cubicLoadUCorePolynomial68_degree_le l A n hA
  have hUlr : Ulr.natDegree ≤ 6 * n - g :=
    cubicLoadURestPolynomial68_degree_le_loadWall
      l alpha beta gamma delta zeta A B c D e n g
      hn hg hwall hA hB hc hD he
  have hEr : Er.natDegree ≤ 6 * n - g :=
    cubicERestPolynomial68_degree_le_loadWall A c e n g
      hn hg hwall hA hc he
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hVl : Vl.natDegree ≤ 7 * n - g := by
    simpa only [Vl] using hloads.2.2.2
  have h1 : (Ulc * derivative Er).natDegree < 12 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 Ulc Er (6 * n) (6 * n - g)
      (12 * n - 1) (by omega) hUlc hEr (by omega)
  have h2 : (Ulr * derivative E).natDegree < 12 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 Ulr E (6 * n - g) (6 * n)
      (12 * n - 1) (by omega) hUlr hE (by omega)
  have h3 : (D * derivative Vl).natDegree < 12 * n - 1 :=
    natDegree_mul_derivative_lt_of_add_sub68 D Vl (5 * n - g) (7 * n - g)
      (12 * n - 1) (by omega) hD hVl (by omega)
  change (Ulc * derivative Er + Ulr * derivative E -
      D * derivative Vl).natDegree < _
  exact natDegree_sub_lt68 (natDegree_add_lt68 h1 h2) h3

/-! ## Load coefficients at the wall indices -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoPolynomial68_coeff_loadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).coeff (10 * n - 1) =
      (35 / 324 : k) * (n : k) * l * A.coeff (2 * n) ^ 5 := by
  rw [cubicLoadRowTwoPolynomial68_eq_lCore_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowTwoRestPolynomial68_degree_lt_loadWall
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hwall hA hB hc hD he), add_zero]
  exact cubicLoadRowTwoLCorePolynomial68_coeff_loadWall l A n hn hA

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowZeroPolynomial68_coeff_loadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowZeroPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).coeff (12 * n - 1) =
      (35 / 1944 : k) * (n : k) * l * A.coeff (2 * n) ^ 6 := by
  rw [cubicLoadRowZeroPolynomial68_eq_lCore_add_rest, coeff_add,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowZeroRestPolynomial68_degree_lt_loadWall
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hwall hA hB hc hD he), add_zero]
  exact cubicLoadRowZeroLCorePolynomial68_coeff_loadWall l A n hn hA

/-! ## Gap casting `2g = n` into the coefficient field -/

theorem firstLoadWall_gap_cast
    (n g : ℕ) (hwall : 2 * g = n) :
    (g : k) = (n : k) / 2 := by
  apply eq_div_of_mul_eq (by norm_num : (2 : k) ≠ 0)
  have h2 : (2 : k) * (g : k) = (n : k) := by exact_mod_cast hwall
  rw [mul_comm]
  exact h2

theorem firstLoadWallTwoScalar68_eq_homogeneous_add_load
    (n g : ℕ) (a b c d e l : k) (hwall : 2 * g = n) :
    firstLoadWallTwoScalar68 (n : k) a b c d e l =
      (8 / 27 : k) * firstSecondaryTwo68 (n : k) (g : k) a b c d e +
        (35 / 324 : k) * (n : k) * l * a ^ 5 := by
  rw [firstLoadWallTwoScalar68_eq_F2_load, firstLoadWall_gap_cast n g hwall]

/-! ## Integrated lower-row coefficients on the wall -/

set_option maxHeartbeats 4000000 in
theorem integratedLowerRowTwoPolynomial68_coeff_loadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
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
          (10 * n - 1) =
      firstLoadWallTwoScalar68 (n : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) l := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.s_eq, hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowTwoPolynomial68_split, coeff_add,
    cubicHomogeneousRowTwoPolynomial68_coeff_loadWall A B c D e n g
      hn hg hwall hA hB hc hD he,
    cubicLoadRowTwoPolynomial68_coeff_loadWall
      l alpha beta gamma delta epsilon zeta eta A B c D e n g
      hn hg hwall hA hB hc hD he,
    firstLoadWallTwoScalar68_eq_homogeneous_add_load n g
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) l hwall]

set_option maxHeartbeats 4000000 in
theorem integratedLowerRowZeroPolynomial68_coeff_loadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      D ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
        (12 * n - 1) =
      firstLoadWallZeroScalar68 (n : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) l := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split, coeff_add,
    cubicHomogeneousRowZeroPolynomial68_coeff_loadWall A B c D e n g
      hn hg hwall hA hB hc hD he,
    cubicLoadRowZeroPolynomial68_coeff_loadWall
      l alpha beta gamma delta epsilon zeta eta A B c D e n g
      hn hg hwall hA hB hc hD he,
    firstLoadWallZeroScalar68_eq_F0_load]

/-! ## Invariant numerators and the polynomial wall-face wrapper -/

set_option maxHeartbeats 3000000 in
theorem polynomialSecondaryInvariantEquations68_loadWall
    (l beta gamma delta epsilon zeta i4 i3 : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
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
    firstLoadWallFourNumerator68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) l = 0 ∧
      firstSecondaryThree68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) = 0 := by
  have ht4 : 8 * n ≠ 0 := by omega
  have ht3 : 9 * n ≠ 0 := by omega
  have hfour := congrArg (fun p : k[X] => p.coeff (8 * n)) hI4
  rw [hC0, hE0, firstIntegralFourPolynomial68_cubicCoordinates,
    cubicFirstIntegralFourPolynomial68_coeff_loadWall
      l beta gamma delta epsilon zeta A B c D e n g hn hg hwall
      hA hB hc hD he] at hfour
  simp only [coeff_C, ite_eq_right ht4] at hfour
  have hthree := congrArg (fun p : k[X] => p.coeff (9 * n)) hI3
  rw [hC0, hE0, firstIntegralThreePolynomial68_cubicCoordinates,
    cubicFirstIntegralThreePolynomial68_coeff_loadWall
      l beta gamma delta epsilon zeta A B c D e n g hn hg hwall
      hA hB hc hD he] at hthree
  simp only [coeff_C, ite_eq_right ht3] at hthree
  constructor
  · have hsc := firstLoadWallFourScalar68_eq_numerator
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) l
    rw [hsc] at hfour
    exact (div_eq_zero_iff.mp hfour).resolve_right (by norm_num)
  · exact (mul_eq_zero.mp hthree).resolve_left (by norm_num)

set_option maxHeartbeats 4000000 in
/-- The literal integrated polynomial lower system supplies all five
equations of the mixed first load wall `2g = n`. -/
theorem integratedPolynomialLowerSystem_firstLoadWallFace68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    FirstLoadWallFace68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) l := by
  obtain ⟨i4, hI4⟩ := hsys.firstFour
  obtain ⟨i3, hI3⟩ := hsys.firstThree
  have hinv := polynomialSecondaryInvariantEquations68_loadWall
    l beta gamma delta epsilon zeta i4 i3 A B C0 c D E e n g
    hn hg hwall hA hB hc hD he hC0 hE0 hI4 hI3
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hrowTwo := hsys.rowTwo
  rw [hC0, hE0] at hrowTwo
  have htwo := congrArg
    (fun p : k[X] => p.coeff (10 * n - 1)) hrowTwo
  rw [integratedLowerRowTwoPolynomial68_coeff_loadWall
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hwall hA hB hc hD he] at htwo
  simp only [coeff_zero] at htwo
  have htwoNum : firstLoadWallTwoNumerator68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) l = 0 := by
    have hsc := firstLoadWallTwoScalar68_eq_numerator (n : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) l
    rw [hsc] at htwo
    have hdiv := div_eq_zero_iff.mp htwo
    have hprod : - (n : k) *
        firstLoadWallTwoNumerator68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) l = 0 :=
      hdiv.resolve_right (by norm_num)
    exact (mul_eq_zero.mp hprod).resolve_left (neg_ne_zero.mpr hncast)
  have hrowOne := hsys.rowOne
  rw [hC0, hE0] at hrowOne
  have hone := congrArg
    (fun p : k[X] => p.coeff (11 * n - 1)) hrowOne
  rw [integratedLowerRowOnePolynomial68_coeff_loadWall
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hwall hA hB hc hD he] at hone
  simp only [coeff_zero] at hone
  have hone0 : firstSecondaryOne68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 :=
    (mul_eq_zero.mp hone).resolve_left (by norm_num)
  have hrowZero := hsys.rowZero
  rw [hC0, hE0] at hrowZero
  have hzero := congrArg
    (fun p : k[X] => p.coeff (12 * n - 1)) hrowZero
  rw [integratedLowerRowZeroPolynomial68_coeff_loadWall
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hwall hA hB hc hD he] at hzero
  have hindex : 12 * n - 1 ≠ 0 := by omega
  simp only [coeff_C, ite_eq_right hindex] at hzero
  have hzeroNum : firstLoadWallZeroNumerator68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) l = 0 := by
    have hsc := firstLoadWallZeroScalar68_eq_numerator (n : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) l
    rw [hsc] at hzero
    have hdiv := div_eq_zero_iff.mp hzero
    have hprod : (A.coeff (2 * n) * (n : k)) *
        firstLoadWallZeroNumerator68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) l = 0 :=
      hdiv.resolve_right (by norm_num)
    have hfactor : A.coeff (2 * n) * (n : k) ≠ 0 :=
      mul_ne_zero ha hncast
    exact (mul_eq_zero.mp hprod).resolve_left hfactor
  exact ⟨hinv.1, hinv.2, htwoNum, hone0, hzeroNum⟩

/-- Direct classified form of the mixed first load wall. -/
theorem integratedPolynomialLowerSystem_firstLoadWallClassified68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    l = 0 ∧ e.coeff (6 * n - g) = 0 ∧
      A.coeff (2 * n) * B.coeff (3 * n - g) =
        3 * D.coeff (5 * n - g) :=
  firstLoadWallFace68_classify_of_two_mul_gap_eq_radius n g
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) l ha hn hwall
    (integratedPolynomialLowerSystem_firstLoadWallFace68
      l alpha beta gamma delta epsilon zeta eta terminal
      A B C0 c D E e n g hn hg hwall hA hB hc hD he ha hC0 hE0 hsys)

end FirstLoadWallRemainder68

#print axioms jacobianRowTwo_eq_core_add_rest
#print axioms jacobianRowZero_eq_core_add_rest
#print axioms cubicLoadRowTwoPolynomial68_eq_lCore_add_rest
#print axioms cubicLoadRowZeroPolynomial68_eq_lCore_add_rest
#print axioms cubicLoadRowTwoRestPolynomial68_degree_lt_loadWall
#print axioms cubicLoadRowZeroRestPolynomial68_degree_lt_loadWall
#print axioms cubicLoadRowTwoPolynomial68_coeff_loadWall
#print axioms cubicLoadRowZeroPolynomial68_coeff_loadWall
#print axioms integratedLowerRowTwoPolynomial68_coeff_loadWall
#print axioms integratedLowerRowZeroPolynomial68_coeff_loadWall
#print axioms polynomialSecondaryInvariantEquations68_loadWall
#print axioms integratedPolynomialLowerSystem_firstLoadWallFace68
#print axioms integratedPolynomialLowerSystem_firstLoadWallClassified68

end Max11DegreeRoutes
