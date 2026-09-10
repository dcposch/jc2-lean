import Grok68FirstGapBoundaryEndgameScratch

/-! # Residual double face on the first-load wall `2g = n`

Untracked working note. No tracked file was edited.

After the classified wall `l = 0`, `ee.coeff(6n-g) = 0` and
`A_top * B_top = 3 * D_top`, the endgame scratch extracts the ordinary
tied-double I4/I3 pair throughout `h ≥ 2g`.  This module supplies the
matching load-free row-zero and row-one coefficients at
`13n-3g-1` and `12n-3g-1`, assembles
`SecondaryResidualTiedDoubleFace68`, and excludes the chamber: the
tracked algebra forces `g = 4n`, which contradicts `2g = n`.  The
vanishing fibre `d = ee = 0` is included by the same four equations.

The existing `of_twoGap` / `of_l_eq_zero` lemmas cannot be cited: their
`2g < n` hypothesis is false on the wall even though the homogeneous
identities remain strict after `l = 0`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FirstGapBoundaryDouble68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Row-zero load cutoff on the wall -/

set_option maxHeartbeats 2000000 in
/-- After `l=0` the heaviest terminal load sits at `11n-g-1 = 21n/2-1`,
strictly below the residual double index `13n-3g-1 = 23n/2-1`. -/
theorem cubicLoadRowZeroPolynomial68_degree_lt_residualDouble_of_firstLoadWall
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadRowZeroPolynomial68 0 alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 13 * n - 3 * g - 1 := by
  let E := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Ul := cubicLoadUPolynomial68 0 alpha beta gamma delta zeta A B c D e
  let Vl := cubicLoadVPolynomial68 0 alpha beta gamma delta epsilon eta
    A B c D e
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hloads := cubicLoadPolynomials68_degreeBounds_of_l_eq_zero_loadWall
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    (by omega) hg hwall hA hB hc hD he'
  have hUl : Ul.natDegree ≤ 5 * n - g := by
    simpa only [Ul] using hloads.2.2.1
  have hVl : Vl.natDegree ≤ 6 * n := by
    simpa only [Vl] using hloads.2.2.2
  have hE : E.natDegree ≤ 6 * n := by
    simp only [E]
    compute_degree
    omega
  have hUlE : (Ul * derivative E).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hDVl : (D * derivative Vl).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  change (Ul * derivative E - D * derivative Vl).natDegree < _
  compute_degree
  omega

/-! ## Homogeneous one-form coefficients on the wall -/

set_option maxHeartbeats 4000000 in
theorem secondaryResidualRowOnePolynomial68_coeff_double_of_firstLoadWall
    (A B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (8 / 27 : k) *
        (3 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * (g : k) *
            d.coeff (5 * n - 2 * g) -
          10 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * (n : k) *
            d.coeff (5 * n - 2 * g) +
          2 * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 * (n : k) *
            c.coeff (4 * n - g) -
          9 * A.coeff (2 * n) * (g : k) * c.coeff (4 * n - g) *
            e.coeff (6 * n - 2 * g) +
          30 * A.coeff (2 * n) * (n : k) * c.coeff (4 * n - g) *
            e.coeff (6 * n - 2 * g) +
          3 * (g : k) * c.coeff (4 * n - g) ^ 3 -
          12 * (n : k) * c.coeff (4 * n - g) ^ 3) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have h1 := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B d
    (4 * n) (3 * n - g) (5 * n - 2 * g) (by omega)
    hA2deg hB hd
  have hi1 : 4 * n + (3 * n - g) + (5 * n - 2 * g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi1, hA2] at h1
  have h2 := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) d B
    (4 * n) (5 * n - 2 * g) (3 * n - g) (by omega)
    hA2deg hd hB
  have hi2 : 4 * n + (5 * n - 2 * g) + (3 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi2, hA2] at h2
  have h2' : (A ^ 2 * derivative B * d).coeff
      (12 * n - 3 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        d.coeff (5 * n - 2 * g) * ((3 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 A B d A
    (2 * n) (3 * n - g) (5 * n - 2 * g) (2 * n) (by omega)
    hA hB hd hA
  have hi3 : 2 * n + (3 * n - g) + (5 * n - 2 * g) + 2 * n - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi3] at h3
  have h3' : (A * derivative A * B * d).coeff
      (12 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        d.coeff (5 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h3
  have h4 := coeff_mul_mul_derivative_at_bounds68 A c e
    (2 * n) (4 * n - g) (6 * n - 2 * g) (by omega) hA hc he
  have hi4 : 2 * n + (4 * n - g) + (6 * n - 2 * g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi4] at h4
  have h5 := coeff_mul_mul_derivative_at_bounds68 A e c
    (2 * n) (6 * n - 2 * g) (4 * n - g) (by omega) hA he hc
  have hi5 : 2 * n + (6 * n - 2 * g) + (4 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi5] at h5
  have h5' : (A * derivative c * e).coeff (12 * n - 3 * g - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (6 * n - 2 * g) * ((4 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h5
  have h6 := coeff_mul_mul_derivative_at_bounds68 (B ^ 2) c A
    (6 * n - 2 * g) (4 * n - g) (2 * n) (by omega)
    hB2deg hc hA
  have hi6 : (6 * n - 2 * g) + (4 * n - g) + 2 * n - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi6, hB2] at h6
  have h6' : (derivative A * B ^ 2 * c).coeff
      (12 * n - 3 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h6
  have h7 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (8 * n - 2 * g) (4 * n - g) (by omega) hc2deg hc
  have hi7 : (8 * n - 2 * g) + (4 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi7, hc2] at h7
  have hlowA : (derivative A * d ^ 2).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowB : (B ^ 2 * derivative e).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowC : (B * c * derivative d).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowD : (B * derivative c * d).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowE : (derivative B * c * d).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowF : (e * derivative e).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hcast3 : (((3 * n - g : ℕ) : k)) = 3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) = 4 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  have hcast5 : (((5 * n - 2 * g : ℕ) : k)) =
      5 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 5 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - 2 * g : ℕ) : k)) =
      6 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 6 * n)]
    push_cast
    rfl
  simp only [secondaryResidualRowOnePolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2', h3', h4, h5', h6', h7,
    coeff_eq_zero_of_natDegree_lt hlowA,
    coeff_eq_zero_of_natDegree_lt hlowB,
    coeff_eq_zero_of_natDegree_lt hlowC,
    coeff_eq_zero_of_natDegree_lt hlowD,
    coeff_eq_zero_of_natDegree_lt hlowE,
    coeff_eq_zero_of_natDegree_lt hlowF, smul_eq_mul]
  rw [hcast3, hcast4, hcast5, hcast6]
  push_cast
  ring

set_option maxHeartbeats 3000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_double_of_firstLoadWall
    (A B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 3 * g - 1) =
      (8 / 27 : k) * (n : k) * A.coeff (2 * n) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            e.coeff (6 * n - 2 * g)) -
          A.coeff (2 * n) * c.coeff (4 * n - g) *
            d.coeff (5 * n - 2 * g) +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2) := by
  have h1 := coeff_mul_mul_mul_derivative_at_bounds68 A B e A
    (2 * n) (3 * n - g) (6 * n - 2 * g) (2 * n) (by omega)
    hA hB he hA
  have hi1 : 2 * n + (3 * n - g) + (6 * n - 2 * g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi1] at h1
  have h1' : (A * derivative A * B * e).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        e.coeff (6 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1
  have h2 := coeff_mul_mul_mul_derivative_at_bounds68 A c d A
    (2 * n) (4 * n - g) (5 * n - 2 * g) (2 * n) (by omega)
    hA hc hd hA
  have hi2 : 2 * n + (4 * n - g) + (5 * n - 2 * g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi2] at h2
  have h2' : (A * derivative A * c * d).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * c.coeff (4 * n - g) *
        d.coeff (5 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 B c c A
    (3 * n - g) (4 * n - g) (4 * n - g) (2 * n) (by omega)
    hB hc hc hA
  have hi3 : (3 * n - g) + (4 * n - g) + (4 * n - g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi3] at h3
  have h3' : (derivative A * B * c ^ 2).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h3
  have hlow1 : (A * B ^ 2 * derivative d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow3 : (derivative A * d * e).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow4 : (B * c * derivative e).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow5 : (B * d * derivative d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow6 : (derivative B * d ^ 2).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow7 : (c * derivative c * d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1', h2', h3',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7, smul_eq_mul]
  push_cast
  ring

/-! ## Tied double face after `l = 0` on the wall -/

theorem firstLoadWallResidualDoubleRowZeroIndex68_gt_fiftyNine
    (n g : ℕ) (hn : 10 ≤ n) (hwall : 2 * g = n) :
    59 < 13 * n - 3 * g - 1 := by
  omega

set_option maxHeartbeats 4000000 in
theorem polynomialSecondaryResidualDoubleFace68_of_firstLoadWall
    (alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowOne :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      lowerRowOnePolynomial68
        (integratedTPolynomial68 0 alpha beta gamma epsilon A B C0 D0 E0)
        (integratedUPolynomial68 0 alpha beta gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
          A B C0 D0 E0) C0 D0 E0 = 0)
    (hrowZero :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      (lowerRowZeroPolynomial68
        (integratedUPolynomial68 0 alpha beta gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
          A B C0 D0 E0) D0 E0).coeff (13 * n - 3 * g - 1) = 0) :
    SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (e.coeff (6 * n - 2 * g)) := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let D0 := (1 / 3 : k) • (A * B) + d
  let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  change lowerRowOnePolynomial68
    (integratedTPolynomial68 0 alpha beta gamma epsilon A B C0 D0 E0)
    (integratedUPolynomial68 0 alpha beta gamma delta zeta A B C0 D0 E0)
    (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
      A B C0 D0 E0) C0 D0 E0 = 0 at hrowOne
  change (lowerRowZeroPolynomial68
    (integratedUPolynomial68 0 alpha beta gamma delta zeta A B C0 D0 E0)
    (integratedVPolynomial68 0 alpha beta gamma delta epsilon eta
      A B C0 D0 E0) D0 E0).coeff (13 * n - 3 * g - 1) = 0 at hrowZero
  have hD : D0.natDegree ≤ 5 * n - g := by
    simp only [D0]
    compute_degree
    omega
  have hinv := polynomialSecondaryResidualDoubleInvariants68_of_firstLoadWall
    beta gamma delta epsilon zeta i4 i3 A B c d e n g
    hg hwall hA hB hc hd he hi4 hi3
  have hfour := hinv.1
  have hthree := hinv.2
  have hcoords := integratedPolynomial68_cubicCoordinates
    0 alpha beta gamma delta epsilon zeta eta A B c D0 e
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrowOne
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split, coeff_add,
    show cubicHomogeneousRowOnePolynomial68 A B c D0 e =
        secondaryResidualRowOnePolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowOnePolynomial68_residualCoordinates A B c d e,
    secondaryResidualRowOnePolynomial68_coeff_double_of_firstLoadWall
      A B c d e n g hg hwall hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowOnePolynomial68_degree_lt_residualDouble_of_firstLoadWall
        alpha beta gamma delta epsilon zeta eta A B c D0 e n g
        hg hwall hA hB hc hD he), add_zero, coeff_zero] at hone
  have hone0 := (mul_eq_zero.mp hone).resolve_left (by norm_num)
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split,
    coeff_add,
    show cubicHomogeneousRowZeroPolynomial68 A B c D0 e =
        secondaryResidualRowZeroPolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowZeroPolynomial68_residualCoordinates A B c d e,
    secondaryResidualRowZeroPolynomial68_coeff_double_of_firstLoadWall
      A B c d e n g hg hwall hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowZeroPolynomial68_degree_lt_residualDouble_of_firstLoadWall
        alpha beta gamma delta epsilon zeta eta A B c D0 e n g
        hg hwall hA hB hc hD he), add_zero] at hrowZero
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfactor : (8 / 27 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 := (mul_eq_zero.mp hrowZero).resolve_left hfactor
  exact ⟨hfour, by linear_combination hthree,
    by linear_combination hzero0, by linear_combination hone0⟩

/-! ## Wall arithmetic on the tied double face -/

theorem firstLoadWall_gap_ne_four_radius
    (n g : ℕ) (hg : 0 < g) (hwall : 2 * g = n) : g ≠ 4 * n := by
  intro h
  rw [h] at hg hwall
  omega

theorem firstLoadWall_three_mul_gap_ne_twelve_radius
    (n g : ℕ) (hg : 0 < g) (hwall : 2 * g = n) : 3 * g ≠ 12 * n := by
  intro h
  rw [← hwall] at h
  omega

theorem secondaryResidualTiedDoubleFace68_impossible_of_firstLoadWall
    (n g : ℕ) (a b c d e : k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hg : 0 < g) (hwall : 2 * g = n)
    (hface : SecondaryResidualTiedDoubleFace68
      (n : k) (g : k) a b c d e) : False := by
  have hcast := secondaryResidualTiedDoubleFace68_forces_gap_eq_four_radius
    (n : k) (g : k) a b c d e ha hb hc hface
  have hnat : g = 4 * n := by exact_mod_cast hcast
  exact firstLoadWall_gap_ne_four_radius n g hg hwall hnat

/-- The ordinary residual double face, including `d = e = 0`, is empty on
the first-load wall `2g = n`.  This is the wall analogue of
`secondaryResidualDoubleFace68_impossible`: the support analysis is the
same, and `g = 4n` is excluded by `2g = n` rather than by `3g < n`. -/
theorem secondaryResidualDoubleFace68_impossible_of_firstLoadWall
    (n g : ℕ) (a b c d e : k)
    (ha : a ≠ 0) (hsupport : b ≠ 0 ∨ c ≠ 0)
    (hg : 0 < g) (hwall : 2 * g = n)
    (hface : SecondaryResidualTiedDoubleFace68
      (n : k) (g : k) a b c d e) : False := by
  have hb : b ≠ 0 := by
    rcases hsupport with hb | hc
    · exact hb
    · intro hb0
      have hd0 : d = 0 := by
        have h := hface.four
        rw [hb0] at h
        have hcd : c * d = 0 := by linear_combination (1 / 9 : k) * h
        exact (mul_eq_zero.mp hcd).resolve_left hc
      have he0 : e = 0 := by
        have h := hface.three
        rw [hb0] at h
        have hce : c * e = 0 := by linear_combination (1 / 3 : k) * h
        exact (mul_eq_zero.mp hce).resolve_left hc
      have hone := hface.one
      rw [hb0, hd0, he0] at hone
      have hcoeff : (3 * (g : k) - 12 * (n : k)) ≠ 0 := by
        intro hz
        have hcast : (3 * g : k) = (12 * n : ℕ) := by
          push_cast
          linear_combination hz
        have hnat : 3 * g = 12 * n := by exact_mod_cast hcast
        exact firstLoadWall_three_mul_gap_ne_twelve_radius n g hg hwall hnat
      have hc3 : c ^ 3 = 0 := by
        have hprod : (3 * (g : k) - 12 * (n : k)) * c ^ 3 = 0 := by
          linear_combination hone
        exact (mul_eq_zero.mp hprod).resolve_left hcoeff
      exact (pow_ne_zero 3 hc) hc3
  have hc : c ≠ 0 := by
    rcases hsupport with hb' | hc
    · intro hc0
      have hd0 : d = 0 := by
        have h := hface.three
        rw [hc0] at h
        have hab : a * b ≠ 0 := mul_ne_zero ha hb'
        have habd : a * b * d = 0 := by linear_combination -h
        exact (mul_eq_zero.mp habd).resolve_left hab
      have he0 : e = 0 := by
        have h := hface.zero
        rw [hc0] at h
        have hab : a * b ≠ 0 := mul_ne_zero ha hb'
        have habe : a * b * e = 0 := by linear_combination -h
        exact (mul_eq_zero.mp habe).resolve_left hab
      have h := hface.four
      rw [hc0, hd0, he0] at h
      have hb3 : b ^ 3 = 0 := by linear_combination -h
      exact (pow_ne_zero 3 hb') hb3
    · exact hc
  by_cases hd : d = 0
  · exact secondaryResidualEAtDoubleFace68_impossible b c e hb hc
      (secondaryResidualEAtDoubleFace68_of_tied
        (n : k) (g : k) a b c d e hb hc hd hface)
  by_cases he : e = 0
  · exact secondaryResidualDAtDoubleFace68_impossible a b c d hb hc
      (secondaryResidualDAtDoubleFace68_of_tied
        (n : k) (g : k) a b c d e hb hc he hface)
  exact secondaryResidualTiedDoubleFace68_impossible_of_firstLoadWall
    n g a b c d e ha hb hc hg hwall hface

/-! ## Canonical expanded wrapper -/

set_option maxHeartbeats 5000000 in
/-- The canonical expanded lower system supplies the complete residual
double face on the first-load wall whenever both residual directions have
gap at least `2g` (including the vanishing fibre). -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualDouble68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g = n)
    (hdouble :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      d.natDegree ≤ 5 * n - 2 * g ∧ ee.natDegree ≤ 6 * n - 2 * g) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    l = 0 ∧
      SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (ee.coeff (6 * n - 2 * g)) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change 2 * g = n at hwall
  change d.natDegree ≤ 5 * n - 2 * g ∧
    ee.natDegree ≤ 6 * n - 2 * g at hdouble
  change l = 0 ∧
    SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g))
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallClassified68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hclass
  have hl : l = 0 := hclass.1
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, hl] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, hl] at hi3c
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hnlarge : 10 ≤ n := by
    simpa only [n] using weightedRadius68_ge_ten A B C0 D E hn
  have h0target : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee).coeff (13 * n - 3 * g - 1) = 0 :=
    expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
      terminal _ _ _ _ _ h0e
      (firstLoadWallResidualDoubleRowZeroIndex68_gt_fiftyNine n g
        hnlarge hwall)
  have h1cubic := h1e
  rw [hCrec, hDrec, hErec, hl] at h1cubic
  have h0cubic := h0target
  rw [hCrec, hDrec, hErec, hl] at h0cubic
  exact ⟨hl,
    polynomialSecondaryResidualDoubleFace68_of_firstLoadWall
      alpha beta gamma delta epsilon zeta eta i4 i3 Ae Be ce d ee n g
      hg hwall hA hB hc hdouble.1 hdouble.2 ha hi4c hi3c h1cubic h0cubic⟩

set_option maxHeartbeats 4000000 in
/-- On the canonical expanded system, the residual double chamber
`h ≥ 2g` of the first-load wall `2g = n` is empty, including the fibre
`d = ee = 0`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualDouble_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g = n)
    (hdouble :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      d.natDegree ≤ 5 * n - 2 * g ∧ ee.natDegree ≤ 6 * n - 2 * g) :
    False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change 2 * g = n at hwall
  have hface :=
    maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualDouble68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdouble)
  change l = 0 ∧
    SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) at hface
  have hboundary :=
    maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallBoundary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) at hboundary
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  exact secondaryResidualDoubleFace68_impossible_of_firstLoadWall n g
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
    (ee.coeff (6 * n - 2 * g)) ha hboundary.2.2.2 hg hwall hface.2

end FirstGapBoundaryDouble68

#print axioms firstLoadWall_gap_ne_four_radius
#print axioms firstLoadWall_three_mul_gap_ne_twelve_radius
#print axioms cubicLoadRowZeroPolynomial68_degree_lt_residualDouble_of_firstLoadWall
#print axioms secondaryResidualRowOnePolynomial68_coeff_double_of_firstLoadWall
#print axioms secondaryResidualRowZeroPolynomial68_coeff_double_of_firstLoadWall
#print axioms polynomialSecondaryResidualDoubleFace68_of_firstLoadWall
#print axioms secondaryResidualDoubleFace68_impossible_of_firstLoadWall
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualDouble68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_firstLoadWallResidualDouble_impossible68

end Max11DegreeRoutes
