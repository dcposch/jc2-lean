import LowScale68SecondaryExtraction

/-! Scratch kernel check of the translated `(6,8)` row-two load cutoff.

Naive `ring_nf` after substituting `D=A*B/3+d` leaves an unnormalized
expression that `compute_degree` cannot close.  This file keeps `D` as a
polynomial of degree at most `5n-g` and reuses the existing load-degree
lemmas, which is enough for the `3g` cutoff under `3g<n`.

The exact six-parameter identity recorded by
`cases/max11_68_row2_load_reduction_20260828.py` is proved afterwards by
linearity in the load scalars plus unit expansions, so `ring` never sees
all eight parameters at once.  The CAS expansion shows that `alpha` and
`eta` cancel.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section RowTwoLoadScratch

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 3000000 in
/-- After translating `D=A*B/3+d`, every constant-load contribution to the
first one-form lies strictly below the next `3g` residual face. -/
theorem cubicLoadRowTwoPolynomial68_degree_lt_cubicFace
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        11 * n - 3 * g - 1 := by
  let D := (1 / 3 : k) • (A * B) + d
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Sl := cubicLoadSPolynomial68 l alpha beta delta A B c
  let Tl := cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D
  let Ul := cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
    A B c D e
  have hn : 0 < n := by omega
  have hsmall' : 2 * g < n := by omega
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hloads := cubicLoadPolynomials68_degreeBounds
    l alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hsmall' hA hB hc hD he'
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
  have hUlC : (Ul * derivative C0).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hTlD : (Tl * derivative D).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hSlE : (Sl * derivative E).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hBVl : (B * derivative Vl).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hC0Ul : (C0 * derivative Ul).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  have hDTl : (D * derivative Tl).natDegree < 11 * n - 3 * g - 1 := by
    compute_degree
    omega
  change (Ul * derivative C0 + (2 : k) • (Tl * derivative D) +
    (3 : k) • (Sl * derivative E) - (3 : k) • (B * derivative Vl) -
    (2 : k) • (C0 * derivative Ul) - D * derivative Tl).natDegree < _
  compute_degree
  omega

/-- Exact load contribution to the first one-form after `D=A*B/3+d`.
The coefficients are the factored CAS expansion; `alpha` and `eta` are
absent because they cancel. -/
def cubicLoadRowTwoTranslatedPolynomial68
    (l beta gamma delta epsilon zeta : k)
    (A B c d e : k[X]) : k[X] :=
  (7 / 1296 * l : k) •
    ((10 : k) • (A ^ 4 * derivative A) +
      (33 : k) • (A ^ 3 * derivative c) -
      (15 : k) • (A ^ 2 * B * derivative B) +
      (72 : k) • (A ^ 2 * c * derivative A) +
      (126 : k) • (A ^ 2 * derivative e) -
      (6 : k) • (A * B ^ 2 * derivative A) +
      (36 : k) • (A * B * derivative d) +
      (108 : k) • (A * c * derivative c) +
      (36 : k) • (A * d * derivative B) +
      (144 : k) • (A * e * derivative A) -
      (90 : k) • (B ^ 2 * derivative c) -
      (180 : k) • (B * c * derivative B) -
      (72 : k) • (B * d * derivative A) +
      (216 : k) • (c * derivative e) +
      (216 : k) • (d * derivative d) +
      (216 : k) • (e * derivative c)) +
  (5 / 72 * beta : k) •
    ((2 : k) • (A ^ 3 * derivative A) +
      (7 : k) • (A ^ 2 * derivative c) -
      (2 : k) • (A * B * derivative B) +
      (8 : k) • (A * c * derivative A) +
      (36 : k) • (A * derivative e) +
      (2 : k) • (B ^ 2 * derivative A) -
      (12 : k) • (B * derivative d) -
      (12 : k) • (c * derivative c) -
      (12 : k) • (d * derivative B)) +
  (2 / 3 * gamma : k) •
    ((2 : k) • (A * derivative d) -
      (2 : k) • (B * derivative c) -
      (2 : k) • (c * derivative B) -
      d * derivative A) +
  (1 / 6 * delta : k) •
    ((2 : k) • (A ^ 2 * derivative A) +
      (9 : k) • (A * derivative c) -
      (9 : k) • (B * derivative B) +
      (18 : k) • derivative e) +
  (1 / 3 * epsilon : k) •
    ((2 : k) • (A * derivative B) -
      B * derivative A +
      (6 : k) • derivative d) +
  (1 / 3 * zeta : k) •
    ((2 : k) • (A * derivative A) +
      (3 : k) • derivative c)

theorem cubicLoadSPolynomial68_add
    (l l' alpha alpha' beta beta' delta delta' : k) (A B c : k[X]) :
    cubicLoadSPolynomial68 (l + l') (alpha + alpha') (beta + beta')
      (delta + delta') A B c =
      cubicLoadSPolynomial68 l alpha beta delta A B c +
        cubicLoadSPolynomial68 l' alpha' beta' delta' A B c := by
  simp only [cubicLoadSPolynomial68, mul_add, add_smul, map_add]
  abel

theorem cubicLoadTPolynomial68_add
    (l l' alpha alpha' beta beta' gamma gamma' epsilon epsilon' : k)
    (A B c D : k[X]) :
    cubicLoadTPolynomial68 (l + l') (alpha + alpha') (beta + beta')
      (gamma + gamma') (epsilon + epsilon') A B c D =
      cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D +
        cubicLoadTPolynomial68 l' alpha' beta' gamma' epsilon' A B c D := by
  simp only [cubicLoadTPolynomial68, mul_add, add_smul, map_add]
  abel

theorem cubicLoadUPolynomial68_add
    (l l' alpha alpha' beta beta' gamma gamma' delta delta' zeta zeta' : k)
    (A B c D e : k[X]) :
    cubicLoadUPolynomial68 (l + l') (alpha + alpha') (beta + beta')
      (gamma + gamma') (delta + delta') (zeta + zeta') A B c D e =
      cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e +
        cubicLoadUPolynomial68 l' alpha' beta' gamma' delta' zeta'
          A B c D e := by
  simp only [cubicLoadUPolynomial68, mul_add, add_smul, map_add]
  abel

theorem cubicLoadVPolynomial68_add
    (l l' alpha alpha' beta beta' gamma gamma' delta delta'
      epsilon epsilon' eta eta' : k)
    (A B c D e : k[X]) :
    cubicLoadVPolynomial68 (l + l') (alpha + alpha') (beta + beta')
      (gamma + gamma') (delta + delta') (epsilon + epsilon') (eta + eta')
      A B c D e =
      cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta A B c D e +
        cubicLoadVPolynomial68 l' alpha' beta' gamma' delta' epsilon' eta'
          A B c D e := by
  simp only [cubicLoadVPolynomial68, mul_add, add_smul, map_add]
  abel

theorem cubicLoadSPolynomial68_smul
    (r l alpha beta delta : k) (A B c : k[X]) :
    cubicLoadSPolynomial68 (r * l) (r * alpha) (r * beta) (r * delta)
      A B c =
      r • cubicLoadSPolynomial68 l alpha beta delta A B c := by
  simp only [cubicLoadSPolynomial68, smul_add, map_mul,
    Polynomial.smul_eq_C_mul]
  ring

theorem cubicLoadTPolynomial68_smul
    (r l alpha beta gamma epsilon : k) (A B c D : k[X]) :
    cubicLoadTPolynomial68 (r * l) (r * alpha) (r * beta) (r * gamma)
      (r * epsilon) A B c D =
      r • cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D := by
  simp only [cubicLoadTPolynomial68, smul_add, map_mul,
    Polynomial.smul_eq_C_mul]
  ring

theorem cubicLoadUPolynomial68_smul
    (r l alpha beta gamma delta zeta : k) (A B c D e : k[X]) :
    cubicLoadUPolynomial68 (r * l) (r * alpha) (r * beta) (r * gamma)
      (r * delta) (r * zeta) A B c D e =
      r • cubicLoadUPolynomial68 l alpha beta gamma delta zeta
        A B c D e := by
  simp only [cubicLoadUPolynomial68, smul_add, map_mul,
    Polynomial.smul_eq_C_mul]
  ring

theorem cubicLoadVPolynomial68_smul
    (r l alpha beta gamma delta epsilon eta : k) (A B c D e : k[X]) :
    cubicLoadVPolynomial68 (r * l) (r * alpha) (r * beta) (r * gamma)
      (r * delta) (r * epsilon) (r * eta) A B c D e =
      r • cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
        A B c D e := by
  simp only [cubicLoadVPolynomial68, smul_add, map_mul,
    Polynomial.smul_eq_C_mul]
  ring

/-- The first one-form as a bilinear expression in the four load pieces. -/
def loadRowTwoCore68 (S T U V B C0 D E : k[X]) : k[X] :=
  U * derivative C0 + (2 : k) • (T * derivative D) +
    (3 : k) • (S * derivative E) - (3 : k) • (B * derivative V) -
    (2 : k) • (C0 * derivative U) - D * derivative T

theorem cubicLoadRowTwoPolynomial68_eq_core
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e =
      loadRowTwoCore68
        (cubicLoadSPolynomial68 l alpha beta delta A B c)
        (cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D)
        (cubicLoadUPolynomial68 l alpha beta gamma delta zeta A B c D e)
        (cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
          A B c D e)
        B ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) := rfl

theorem loadRowTwoCore68_add
    (S1 S2 T1 T2 U1 U2 V1 V2 B C0 D E : k[X]) :
    loadRowTwoCore68 (S1 + S2) (T1 + T2) (U1 + U2) (V1 + V2) B C0 D E =
      loadRowTwoCore68 S1 T1 U1 V1 B C0 D E +
        loadRowTwoCore68 S2 T2 U2 V2 B C0 D E := by
  simp only [loadRowTwoCore68, derivative_add, mul_add, add_mul, smul_add]
  abel

theorem loadRowTwoCore68_smul
    (r : k) (S T U V B C0 D E : k[X]) :
    loadRowTwoCore68 (r • S) (r • T) (r • U) (r • V) B C0 D E =
      r • loadRowTwoCore68 S T U V B C0 D E := by
  simp only [loadRowTwoCore68, derivative_smul, smul_add, smul_sub,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm r]
  try abel

theorem cubicLoadRowTwoPolynomial68_add
    (l l' alpha alpha' beta beta' gamma gamma' delta delta'
      epsilon epsilon' zeta zeta' eta eta' : k)
    (A B c D e : k[X]) :
    cubicLoadRowTwoPolynomial68 (l + l') (alpha + alpha') (beta + beta')
      (gamma + gamma') (delta + delta') (epsilon + epsilon')
      (zeta + zeta') (eta + eta') A B c D e =
      cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        A B c D e +
      cubicLoadRowTwoPolynomial68 l' alpha' beta' gamma' delta' epsilon'
        zeta' eta' A B c D e := by
  simp only [cubicLoadRowTwoPolynomial68_eq_core, cubicLoadSPolynomial68_add,
    cubicLoadTPolynomial68_add, cubicLoadUPolynomial68_add,
    cubicLoadVPolynomial68_add, loadRowTwoCore68_add]

theorem cubicLoadRowTwoPolynomial68_smul
    (r l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowTwoPolynomial68 (r * l) (r * alpha) (r * beta) (r * gamma)
      (r * delta) (r * epsilon) (r * zeta) (r * eta) A B c D e =
      r • cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon
        zeta eta A B c D e := by
  simp only [cubicLoadRowTwoPolynomial68_eq_core, cubicLoadSPolynomial68_smul,
    cubicLoadTPolynomial68_smul, cubicLoadUPolynomial68_smul,
    cubicLoadVPolynomial68_smul, loadRowTwoCore68_smul]

private theorem cubicLoadRowTwoPolynomial68_sumEight
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e =
      cubicLoadRowTwoPolynomial68 l 0 0 0 0 0 0 0 A B c D e +
      cubicLoadRowTwoPolynomial68 0 alpha 0 0 0 0 0 0 A B c D e +
      cubicLoadRowTwoPolynomial68 0 0 beta 0 0 0 0 0 A B c D e +
      cubicLoadRowTwoPolynomial68 0 0 0 gamma 0 0 0 0 A B c D e +
      cubicLoadRowTwoPolynomial68 0 0 0 0 delta 0 0 0 A B c D e +
      cubicLoadRowTwoPolynomial68 0 0 0 0 0 epsilon 0 0 A B c D e +
      cubicLoadRowTwoPolynomial68 0 0 0 0 0 0 zeta 0 A B c D e +
      cubicLoadRowTwoPolynomial68 0 0 0 0 0 0 0 eta A B c D e := by
  have h1 := cubicLoadRowTwoPolynomial68_add
    l 0 0 alpha 0 beta 0 gamma 0 delta 0 epsilon 0 zeta 0 eta
    A B c D e
  have h2 := cubicLoadRowTwoPolynomial68_add
    0 0 alpha 0 0 beta 0 gamma 0 delta 0 epsilon 0 zeta 0 eta
    A B c D e
  have h3 := cubicLoadRowTwoPolynomial68_add
    0 0 0 0 beta 0 0 gamma 0 delta 0 epsilon 0 zeta 0 eta
    A B c D e
  have h4 := cubicLoadRowTwoPolynomial68_add
    0 0 0 0 0 0 gamma 0 0 delta 0 epsilon 0 zeta 0 eta
    A B c D e
  have h5 := cubicLoadRowTwoPolynomial68_add
    0 0 0 0 0 0 0 0 delta 0 0 epsilon 0 zeta 0 eta
    A B c D e
  have h6 := cubicLoadRowTwoPolynomial68_add
    0 0 0 0 0 0 0 0 0 0 epsilon 0 0 zeta 0 eta
    A B c D e
  have h7 := cubicLoadRowTwoPolynomial68_add
    0 0 0 0 0 0 0 0 0 0 0 0 zeta 0 0 eta
    A B c D e
  simp only [add_zero, zero_add] at h1 h2 h3 h4 h5 h6 h7
  rw [h1, h2, h3, h4, h5, h6, h7]
  abel

private theorem cubicLoadRowTwoPolynomial68_axis_smul
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowTwoPolynomial68 l 0 0 0 0 0 0 0 A B c D e =
      l • cubicLoadRowTwoPolynomial68 1 0 0 0 0 0 0 0 A B c D e ∧
    cubicLoadRowTwoPolynomial68 0 alpha 0 0 0 0 0 0 A B c D e =
      alpha • cubicLoadRowTwoPolynomial68 0 1 0 0 0 0 0 0 A B c D e ∧
    cubicLoadRowTwoPolynomial68 0 0 beta 0 0 0 0 0 A B c D e =
      beta • cubicLoadRowTwoPolynomial68 0 0 1 0 0 0 0 0 A B c D e ∧
    cubicLoadRowTwoPolynomial68 0 0 0 gamma 0 0 0 0 A B c D e =
      gamma • cubicLoadRowTwoPolynomial68 0 0 0 1 0 0 0 0 A B c D e ∧
    cubicLoadRowTwoPolynomial68 0 0 0 0 delta 0 0 0 A B c D e =
      delta • cubicLoadRowTwoPolynomial68 0 0 0 0 1 0 0 0 A B c D e ∧
    cubicLoadRowTwoPolynomial68 0 0 0 0 0 epsilon 0 0 A B c D e =
      epsilon • cubicLoadRowTwoPolynomial68 0 0 0 0 0 1 0 0 A B c D e ∧
    cubicLoadRowTwoPolynomial68 0 0 0 0 0 0 zeta 0 A B c D e =
      zeta • cubicLoadRowTwoPolynomial68 0 0 0 0 0 0 1 0 A B c D e ∧
    cubicLoadRowTwoPolynomial68 0 0 0 0 0 0 0 eta A B c D e =
      eta • cubicLoadRowTwoPolynomial68 0 0 0 0 0 0 0 1 A B c D e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using cubicLoadRowTwoPolynomial68_smul
      l 1 0 0 0 0 0 0 0 A B c D e
  · simpa using cubicLoadRowTwoPolynomial68_smul
      alpha 0 1 0 0 0 0 0 0 A B c D e
  · simpa using cubicLoadRowTwoPolynomial68_smul
      beta 0 0 1 0 0 0 0 0 A B c D e
  · simpa using cubicLoadRowTwoPolynomial68_smul
      gamma 0 0 0 1 0 0 0 0 A B c D e
  · simpa using cubicLoadRowTwoPolynomial68_smul
      delta 0 0 0 0 1 0 0 0 A B c D e
  · simpa using cubicLoadRowTwoPolynomial68_smul
      epsilon 0 0 0 0 0 1 0 0 A B c D e
  · simpa using cubicLoadRowTwoPolynomial68_smul
      zeta 0 0 0 0 0 0 1 0 A B c D e
  · simpa using cubicLoadRowTwoPolynomial68_smul
      eta 0 0 0 0 0 0 0 1 A B c D e

private theorem row_two_load_unit_eq {p q : k[X]}
    (h : algebraMap k[X] (RatFunc k) p = algebraMap k[X] (RatFunc k) q) :
    p = q :=
  (FaithfulSMul.algebraMap_injective k[X] (RatFunc k)) h

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowTwoPolynomial68_unit_l
    (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 1 0 0 0 0 0 0 0
      A B c ((1 / 3 : k) • (A * B) + d) e =
      cubicLoadRowTwoTranslatedPolynomial68 1 0 0 0 0 0 A B c d e := by
  apply row_two_load_unit_eq
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    cubicLoadRowTwoTranslatedPolynomial68, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_C, derivative_one, zero_mul, mul_zero,
    zero_add, add_zero, one_mul, mul_one, zero_smul, smul_zero, one_smul,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoPolynomial68_unit_alpha
    (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 1 0 0 0 0 0 0
      A B c ((1 / 3 : k) • (A * B) + d) e = 0 := by
  apply row_two_load_unit_eq
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, derivative_one, zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one,
    zero_smul, smul_zero, one_smul, Polynomial.C_eq_natCast,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowTwoPolynomial68_unit_beta
    (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 0 1 0 0 0 0 0
      A B c ((1 / 3 : k) • (A * B) + d) e =
      cubicLoadRowTwoTranslatedPolynomial68 0 1 0 0 0 0 A B c d e := by
  apply row_two_load_unit_eq
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    cubicLoadRowTwoTranslatedPolynomial68, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_C, derivative_one, zero_mul, mul_zero,
    zero_add, add_zero, one_mul, mul_one, zero_smul, smul_zero, one_smul,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowTwoPolynomial68_unit_gamma
    (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 0 0 1 0 0 0 0
      A B c ((1 / 3 : k) • (A * B) + d) e =
      cubicLoadRowTwoTranslatedPolynomial68 0 0 1 0 0 0 A B c d e := by
  apply row_two_load_unit_eq
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    cubicLoadRowTwoTranslatedPolynomial68, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_C, derivative_one, zero_mul, mul_zero,
    zero_add, add_zero, one_mul, mul_one, zero_smul, smul_zero, one_smul,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowTwoPolynomial68_unit_delta
    (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 0 0 0 1 0 0 0
      A B c ((1 / 3 : k) • (A * B) + d) e =
      cubicLoadRowTwoTranslatedPolynomial68 0 0 0 1 0 0 A B c d e := by
  apply row_two_load_unit_eq
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    cubicLoadRowTwoTranslatedPolynomial68, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_C, derivative_one, zero_mul, mul_zero,
    zero_add, add_zero, one_mul, mul_one, zero_smul, smul_zero, one_smul,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowTwoPolynomial68_unit_epsilon
    (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 0 0 0 0 1 0 0
      A B c ((1 / 3 : k) • (A * B) + d) e =
      cubicLoadRowTwoTranslatedPolynomial68 0 0 0 0 1 0 A B c d e := by
  apply row_two_load_unit_eq
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    cubicLoadRowTwoTranslatedPolynomial68, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_C, derivative_one, zero_mul, mul_zero,
    zero_add, add_zero, one_mul, mul_one, zero_smul, smul_zero, one_smul,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowTwoPolynomial68_unit_zeta
    (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 0 0 0 0 0 1 0
      A B c ((1 / 3 : k) • (A * B) + d) e =
      cubicLoadRowTwoTranslatedPolynomial68 0 0 0 0 0 1 A B c d e := by
  apply row_two_load_unit_eq
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    cubicLoadRowTwoTranslatedPolynomial68, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_C, derivative_one, zero_mul, mul_zero,
    zero_add, add_zero, one_mul, mul_one, zero_smul, smul_zero, one_smul,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoPolynomial68_unit_eta
    (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 0 0 0 0 0 0 1
      A B c ((1 / 3 : k) • (A * B) + d) e = 0 := by
  apply row_two_load_unit_eq
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadSPolynomial68,
    cubicLoadTPolynomial68, cubicLoadUPolynomial68, cubicLoadVPolynomial68,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, derivative_one, zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one,
    zero_smul, smul_zero, one_smul, Polynomial.C_eq_natCast,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul,
    map_zero]
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1024 in
/-- Substituting `D=A*B/3+d` yields the six-parameter translated load. -/
theorem cubicLoadRowTwoPolynomial68_translatedCoordinates
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) :
    cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e =
      cubicLoadRowTwoTranslatedPolynomial68
        l beta gamma delta epsilon zeta A B c d e := by
  have haxes := cubicLoadRowTwoPolynomial68_axis_smul
    l alpha beta gamma delta epsilon zeta eta A B c
    ((1 / 3 : k) • (A * B) + d) e
  rw [cubicLoadRowTwoPolynomial68_sumEight, haxes.1, haxes.2.1, haxes.2.2.1,
    haxes.2.2.2.1, haxes.2.2.2.2.1, haxes.2.2.2.2.2.1,
    haxes.2.2.2.2.2.2.1, haxes.2.2.2.2.2.2.2]
  rw [cubicLoadRowTwoPolynomial68_unit_l,
    cubicLoadRowTwoPolynomial68_unit_alpha,
    cubicLoadRowTwoPolynomial68_unit_beta,
    cubicLoadRowTwoPolynomial68_unit_gamma,
    cubicLoadRowTwoPolynomial68_unit_delta,
    cubicLoadRowTwoPolynomial68_unit_epsilon,
    cubicLoadRowTwoPolynomial68_unit_zeta,
    cubicLoadRowTwoPolynomial68_unit_eta]
  simp only [smul_zero, add_zero]
  apply row_two_load_unit_eq
  simp only [cubicLoadRowTwoTranslatedPolynomial68, smul_add, smul_sub,
    smul_smul, Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_neg,
    map_zero, map_one, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one, map_neg, map_mul]
  ring

#print axioms cubicLoadRowTwoPolynomial68_degree_lt_cubicFace
#print axioms cubicLoadRowTwoPolynomial68_translatedCoordinates

end RowTwoLoadScratch

end Max11DegreeRoutes
