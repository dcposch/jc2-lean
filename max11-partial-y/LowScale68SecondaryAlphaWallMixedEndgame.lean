import LowScale68SecondaryAlphaWallRowTwoLoad
import LowScale68SecondaryResidualRowOneFaces
import LowScale68SecondaryResidualDescent
import LowScale68SecondaryDeepGapResidualOneForms

/-! # Mixed residual endgame on the alpha wall `g = n`

I4 being constant forces `Q = (3/8)(C i4 - I4_load)`, so after `l = 0`
one has `Q.natDegree ≤ 6n` and `Q.coeff(6n) = -(5/192) beta a^3`.
Residual I3 is likewise of degree `≤ 6n`.

On a middle residual gap `g < h < 2g` this yields an exact finite
scalar system in both remaining chambers:

* right `3g < 2h`: mixed row two
  `(-4/27)((25 n / 32) beta a^4 - (64 n / 3) a b^3) = -(5 n / 18) beta a^4`
  together with load-free row one `(-32 n / 3) c^3 = 0`;
* balanced `2h = 3g`: the same Q-feed plus the ordinary `de` face, and
  load-free row one `(-64 n / 3) c^3 = 0`.

Load-free row one forces `c = 0`, then the middle discriminant forces
`b = 0`, against support.  Left remains the ordinary `de` face.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlphaWallMixedEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Degree helpers -/

private theorem residual_natDegree_mul_derivative_le68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 0 < v) (hq : q.natDegree ≤ v) :
    (p * derivative q).natDegree ≤ u + v - 1 := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (by omega)
  have hmul := natDegree_mul_le_of_le hu hd
  omega

private theorem residual_natDegree_derivative_mul_le68
    (p q : k[X]) (u v : ℕ)
    (hu0 : 0 < u) (hu : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (derivative p * q).natDegree ≤ u + v - 1 := by
  have hd : (derivative p).natDegree ≤ u - 1 :=
    (natDegree_derivative_le p).trans (by omega)
  have hmul := natDegree_mul_le_of_le hd hq
  omega

/-! ## I4 load and the incidence defect `Q` -/

theorem residualIncidenceQ68_eq_I4 (B c d e : k[X]) :
    secondaryResidualInvariantFourPolynomial68 B c d e =
      (8 / 3 : k) • residualIncidenceQ68 B c d e := by
  unfold residualIncidenceQ68
  exact secondaryResidualInvariantFourPolynomial68_eq_incidenceDefect B c d e

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_le_sixRadius_of_alphaWall
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree ≤ 6 * n := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem residualIncidenceQ68_eq_I4load_of_alphaWall
    (beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    residualIncidenceQ68 B c d e =
      (3 / 8 : k) •
        (C i4 -
          secondaryLoadInvariantFourPolynomial68
            0 beta gamma delta epsilon zeta A B c
              ((1 / 3 : k) • (A * B) + d) e) := by
  let D := (1 / 3 : k) • (A * B) + d
  let Q := residualIncidenceQ68 B c d e
  let load := secondaryLoadInvariantFourPolynomial68
    0 beta gamma delta epsilon zeta A B c D e
  have hsplit := hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    cubicFirstIntegralFourPolynomial68_residualCoordinates,
    residualIncidenceQ68_eq_I4] at hsplit
  change (8 / 3 : k) • Q + load = C i4 at hsplit
  have hcore : (8 / 3 : k) • Q = C i4 - load :=
    eq_sub_of_add_eq hsplit
  calc
    Q = (3 / 8 : k) • ((8 / 3 : k) • Q) := by
      rw [smul_smul]
      norm_num
    _ = (3 / 8 : k) • (C i4 - load) := by rw [hcore]

set_option maxHeartbeats 2000000 in
theorem residualIncidenceQ68_degree_le_sixRadius_of_alphaWall
    (beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g : ℕ) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hQeq := residualIncidenceQ68_eq_I4load_of_alphaWall
    beta gamma delta epsilon zeta i4 A B c d e hi4
  have hload :=
    secondaryLoadInvariantFourPolynomial68_degree_le_sixRadius_of_alphaWall
      beta gamma delta epsilon zeta A B c D e n g hwall hA hB hc hD he
  rw [hQeq]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem residualIncidenceQ68_coeff_sixRadius_of_alphaWall
    (beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : ((1 / 3 : k) • (A * B) + d).natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (residualIncidenceQ68 B c d e).coeff (6 * n) =
      -((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hQeq := residualIncidenceQ68_eq_I4load_of_alphaWall
    beta gamma delta epsilon zeta i4 A B c d e hi4
  have hload :=
    secondaryLoadInvariantFourPolynomial68_coeff_sixRadius_of_alphaWall
      0 beta gamma delta epsilon zeta A B c D e n g hn (by omega) rfl hwall
      hA hB hc hD he
  have hindex : 6 * n ≠ 0 := by omega
  rw [hQeq, coeff_smul, coeff_sub, coeff_C, if_neg hindex, smul_eq_mul]
  rw [show D = (1 / 3 : k) • (A * B) + d from rfl] at hload
  rw [hload]
  ring

/-! ## Residual I3 degree after `l = 0` -/

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_le_sixRadius_of_alphaWall
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantThreePolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree ≤ 6 * n := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_eq_I3load_of_alphaWall
    (beta gamma delta epsilon zeta i3 : k) (A B c d e : k[X])
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    secondaryResidualInvariantThreePolynomial68 A B c d e =
      C i3 -
        secondaryLoadInvariantThreePolynomial68
          0 beta gamma delta epsilon zeta A B c
            ((1 / 3 : k) • (A * B) + d) e := by
  let D := (1 / 3 : k) • (A * B) + d
  let load := secondaryLoadInvariantThreePolynomial68
    0 beta gamma delta epsilon zeta A B c D e
  have hsplit := hi3
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    cubicFirstIntegralThreePolynomial68_residualCoordinates] at hsplit
  exact eq_sub_of_add_eq hsplit

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_degree_le_sixRadius_of_alphaWall
    (beta gamma delta epsilon zeta i3 : k) (A B c d e : k[X])
    (n g : ℕ) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      6 * n := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have heq := secondaryResidualInvariantThreePolynomial68_eq_I3load_of_alphaWall
    beta gamma delta epsilon zeta i3 A B c d e hi3
  have hload :=
    secondaryLoadInvariantThreePolynomial68_degree_le_sixRadius_of_alphaWall
      beta gamma delta epsilon zeta A B c D e n g hwall hA hB hc hD he
  rw [heq]
  compute_degree
  omega

theorem secondaryResidualInvariantThreePolynomial68_degree_lt_cubicFace_of_alphaWall
    (beta gamma delta epsilon zeta i3 : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n) (hwall : g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree <
      10 * n - 3 * g := by
  have hle :=
    secondaryResidualInvariantThreePolynomial68_degree_le_sixRadius_of_alphaWall
      beta gamma delta epsilon zeta i3 A B c d e n g hwall
      hA hB hc hd he hi3
  have hlt : 6 * n < 10 * n - 3 * g := by omega
  exact hle.trans_lt hlt

/-! ## Field algebra for the mixed cubic faces -/

theorem alphaWallQInnerScalar68 (N a q0 : k) :
    (-6 : k) * (a * q0 * (6 * N)) + (3 : k) * ((2 * N) * a * q0) =
      (-30 : k) * N * a * q0 := by
  ring

theorem alphaWallQInner_of_I4load68 (N a beta : k) :
    (-30 : k) * N * a * (-((5 / 192 : k) * beta * a ^ 3)) =
      (25 / 32 : k) * N * beta * a ^ 4 := by
  ring

theorem alphaWallRowOneRightInnerScalar68 (N a b c : k)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0) :
    (-2 : k) * (a * b ^ 2 * c * ((9 : k) * N)) +
        (6 : k) * (c ^ 3 * ((3 : k) * N)) =
      (72 : k) * N * c ^ 3 := by
  have hab : a * b ^ 2 = -((3 : k) * c ^ 2) := by linear_combination hdisc
  calc
    (-2 : k) * (a * b ^ 2 * c * ((9 : k) * N)) +
        (6 : k) * (c ^ 3 * ((3 : k) * N))
        = (-2 : k) * ((a * b ^ 2) * c * ((9 : k) * N)) +
            (18 : k) * N * c ^ 3 := by ring
    _ = (-2 : k) * ((-((3 : k) * c ^ 2)) * c * ((9 : k) * N)) +
            (18 : k) * N * c ^ 3 := by rw [hab]
    _ = (72 : k) * N * c ^ 3 := by ring

theorem alphaWallRowOneRightScalar68 (N a b c : k)
    (hdisc : a * b ^ 2 + (3 : k) * c ^ 2 = 0) :
    (-4 / 27 : k) *
        ((-2 : k) * (a * b ^ 2 * c * ((9 : k) * N)) +
          (6 : k) * (c ^ 3 * ((3 : k) * N))) =
      (-32 / 3 : k) * N * c ^ 3 := by
  rw [alphaWallRowOneRightInnerScalar68 N a b c hdisc]
  ring

theorem alphaWallRowOneRightScalar_ne_zero68 (N c : k)
    (hN : N ≠ 0) (hc : c ≠ 0) :
    (-32 / 3 : k) * N * c ^ 3 ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) hN) (pow_ne_zero 3 hc)

/-! ## Mixed residual row two at `8n-1` -/

set_option maxHeartbeats 2000000 in
theorem residualRowTwoInner_de_degree_le68_of_alphaWall
    (d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hwall : g = n)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (derivative (d * e)).natDegree ≤ 11 * n - 2 * h - 1 := by
  have hprod := natDegree_mul_le_of_le hd he
  have hsum : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  rw [hsum] at hprod
  have hder := natDegree_derivative_le (d * e)
  omega

set_option maxHeartbeats 4000000 in
/-- On `3g<2h`, residual row two at the cubic index is the Q-feed from
`beta A^3` plus the ordinary `B,c` core. -/
theorem residualRowTwo_coeff_rightChamber_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (beta : k)
    (hq0 : (residualIncidenceQ68 B c d e).coeff (6 * n) =
      -((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3))
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 3 * g - 1) =
      (-4 / 27 : k) *
        ((25 / 32 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 +
          (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
            A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 3 * g - 1
  have hQle : (A * derivative Q).natDegree ≤ idx := by
    have h := residual_natDegree_mul_derivative_le68 A Q (2 * n) (6 * n)
      hA (by omega) hQ
    have hi : 2 * n + 6 * n - 1 = idx := by dsimp [idx]; omega
    simpa only [hi] using h
  have hQ'le : (derivative A * Q).natDegree ≤ idx := by
    have h := residual_natDegree_derivative_mul_le68 A Q (2 * n) (6 * n)
      (by omega) hA hQ
    have hi : 2 * n + 6 * n - 1 = idx := by dsimp [idx]; omega
    simpa only [hi] using h
  have hAQ := coeff_mul_derivative_at_bounds68 A Q (2 * n) (6 * n)
    (by omega) hA hQ
  have hiAQ : 2 * n + 6 * n - 1 = idx := by dsimp [idx]; omega
  rw [hiAQ] at hAQ
  have hA3 := coeff_mul_derivative_at_bounds68 Q A (6 * n) (2 * n)
    (by omega) hQ hA
  have hiA3 : 6 * n + 2 * n - 1 = idx := by dsimp [idx]; omega
  rw [hiA3] at hA3
  have hA3' : (derivative A * Q).coeff idx =
      A.coeff (2 * n) * Q.coeff (6 * n) * ((2 * n : ℕ) : k) := by
    rw [show (derivative A * Q).coeff idx = (Q * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hA3
  have hBd := residualRowTwoInner_Bd_degree_le68_of_alphaWall B d n g h
    hg hgh hh hwall hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hde := residualRowTwoInner_de_degree_le68_of_alphaWall d e n g h
    hg hgh hh hwall hd he
  have hde' : (derivative (d * e)).natDegree < idx := by
    dsimp [idx]
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hAB := coeff_mul_mul_derivative_at_bounds68 A (B ^ 2) B
    (2 * n) (6 * n - 2 * g) (3 * n - g) (by omega) hA hB2deg hB
  have hiAB : 2 * n + (6 * n - 2 * g) + (3 * n - g) - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiAB, hB2] at hAB
  have hABpow : (A * B ^ 2 * derivative B).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k) := by
    rw [hAB]
    ring
  have hB3deg : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hB3 : (B ^ 3).coeff (9 * n - 3 * g) =
      B.coeff (3 * n - g) ^ 3 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 3 hB
    have hi : 3 * (3 * n - g) = 9 * n - 3 * g := by omega
    simpa only [hi] using h
  have hA3B := coeff_mul_derivative_at_bounds68 (B ^ 3) A
    (9 * n - 3 * g) (2 * n) (by omega) hB3deg hA
  have hiA3B : (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiA3B, hB3] at hA3B
  have hA3B' : (derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B ^ 3).coeff idx =
        (B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hA3B
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBcdeg : (B * c ^ 2).natDegree ≤ 11 * n - 3 * g := by
    have h := natDegree_mul_le_of_le hB hc2deg
    have hi : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
    rwa [hi] at h
  have hBccoeff := coeff_mul_at_bounds68 B (c ^ 2)
    (3 * n - g) (8 * n - 2 * g) hB hc2deg
  have hiBc : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
  rw [hiBc, hc2] at hBccoeff
  have hBc := coeff_derivative_at_bound68 (B * c ^ 2)
    (11 * n - 3 * g) (by omega)
  rw [hBccoeff] at hBc
  have hcast6 : (((6 * n : ℕ) : k)) = (6 : k) * (n : k) := by
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have hcast3 : (((3 * n - g : ℕ) : k)) =
      (3 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast11 : (((11 * n - 3 * g : ℕ) : k)) =
      (11 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 11 * n)]
    push_cast
    rfl
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have h0de : ((-18 : k) • derivative (d * e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hde', mul_zero]
  have hQsm : ((-6 : k) • (A * derivative Q)).coeff idx =
      (-6 : k) * (A.coeff (2 * n) * Q.coeff (6 * n) *
        ((6 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hAQ]
  have hQ'sm : ((3 : k) • (derivative A * Q)).coeff idx =
      (3 : k) * (A.coeff (2 * n) * Q.coeff (6 * n) *
        ((2 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hA3']
  have hABsm : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx =
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((3 * n - g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hABpow]
  have hA3sm : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx =
      (-2 / 3 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hA3B']
  have hBcsm : ((6 : k) • derivative (B * c ^ 2)).coeff idx =
      (6 : k) * (B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 *
        ((11 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hBc]
  have hQpart :
      ((-6 : k) • (A * derivative Q)).coeff idx +
        ((3 : k) • (derivative A * Q)).coeff idx =
        (25 / 32 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 := by
    rw [hQsm, hQ'sm, hcast6, hcast2, hq0]
    trans ((-30 : k) * (n : k) * A.coeff (2 * n) *
      (-((5 / 192 : k) * beta * A.coeff (2 * n) ^ 3)))
    · ring
    exact alphaWallQInner_of_I4load68 (n : k) (A.coeff (2 * n)) beta
  have hcore :
      ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx +
        ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx +
        ((6 : k) • derivative (B * c ^ 2)).coeff idx =
        (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
          A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
    rw [hABsm, hA3sm, hBcsm, hcast3, hcast2, hcast11]
    have hsc := residualRowTwoRightCoreScalar68_of_disc (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g)) hdisc
    convert hsc using 1
    ring
  have hinner : inner.coeff idx =
      (25 / 32 : k) * (n : k) * beta * A.coeff (2 * n) ^ 4 +
        (-8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
          A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Bd, h0de]
    linear_combination hQpart + hcore
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]

/-! ## Load-free residual row one at `9n-1` -/

set_option maxHeartbeats 6000000 in
/-- On `3g<2h`, residual row one is the `A B^2 c` / `c^3` core. -/
theorem residualRowOne_coeff_rightChamber_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      6 * n) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (-4 / 27 : k) *
        ((-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
            c.coeff (4 * n - g) * ((9 * n : ℕ) : k)) +
          (6 : k) * (c.coeff (4 * n - g) ^ 3 * ((3 * n : ℕ) : k))) := by
  let I3 := secondaryResidualInvariantThreePolynomial68 A B c d e
  set idx := 12 * n - 3 * g - 1
  have hI3low : (A * derivative I3).natDegree < idx := by
    have h := residual_natDegree_mul_derivative_le68 A I3 (2 * n) (6 * n)
      hA (by omega) hI3
    have hi : 2 * n + 6 * n - 1 = 8 * n - 1 := by omega
    have hle : (A * derivative I3).natDegree ≤ 8 * n - 1 := by
      simpa only [hi] using h
    have hlt : 8 * n - 1 < idx := by dsimp [idx]; omega
    exact hle.trans_lt hlt
  have hd2deg : (A * d ^ 2).natDegree ≤ 12 * n - 2 * h := by
    have hd2 : (d ^ 2).natDegree ≤ 10 * n - 2 * h := by
      compute_degree
      omega
    have hprod := natDegree_mul_le_of_le hA hd2
    have hsum : 2 * n + (10 * n - 2 * h) = 12 * n - 2 * h := by omega
    rwa [hsum] at hprod
  have hAd2 : (derivative (A * d ^ 2)).natDegree < idx := by
    have hder := natDegree_derivative_le (A * d ^ 2)
    have hle : (derivative (A * d ^ 2)).natDegree ≤ 12 * n - 2 * h - 1 := by
      omega
    have hlt : 12 * n - 2 * h - 1 < idx := by dsimp [idx]; omega
    exact hle.trans_lt hlt
  have hee : (e * derivative e).natDegree < idx := by
    have hd' : (derivative e).natDegree ≤ 6 * n - h - 1 :=
      (natDegree_derivative_le e).trans (by omega)
    have hprod := natDegree_mul_le_of_le he hd'
    have hsum : (6 * n - h) + (6 * n - h - 1) = 12 * n - 2 * h - 1 := by omega
    have hle : (e * derivative e).natDegree ≤ 12 * n - 2 * h - 1 := by
      simpa only [hsum] using hprod
    have hlt : 12 * n - 2 * h - 1 < idx := by dsimp [idx]; omega
    exact hle.trans_lt hlt
  have hlowFace : 12 * n - 2 * g - h - 1 < idx := by
    dsimp [idx]
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have hB2pow := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using hB2pow
  have hAB2ccoeff := coeff_mul_mul_at_bounds68 A (B ^ 2) c
    (2 * n) (6 * n - 2 * g) (4 * n - g) hA hB2deg hc
  have hiAB2c : 2 * n + (6 * n - 2 * g) + (4 * n - g) = 12 * n - 3 * g :=
    by omega
  rw [hiAB2c, hB2] at hAB2ccoeff
  have hAB2cder := coeff_derivative_at_bound68 (A * B ^ 2 * c)
    (12 * n - 3 * g) (by omega)
  rw [hAB2ccoeff] at hAB2cder
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hc3 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (8 * n - 2 * g) (4 * n - g) (by omega) hc2deg hc
  have hic3 : (8 * n - 2 * g) + (4 * n - g) - 1 = idx := by
    dsimp [idx]; omega
  rw [hic3, hc2] at hc3
  have hlowBcd : (derivative (B * c * d)).natDegree < idx := by
    have hBc : (B * c).natDegree ≤ (3 * n - g) + (4 * n - g) :=
      natDegree_mul_le_of_le hB hc
    have hprod := natDegree_mul_le_of_le hBc hd
    have hsum : (3 * n - g) + (4 * n - g) + (5 * n - h) =
        12 * n - 2 * g - h := by omega
    rw [hsum] at hprod
    have hder := natDegree_derivative_le (B * c * d)
    have hle : (derivative (B * c * d)).natDegree ≤
        12 * n - 2 * g - h - 1 := by omega
    exact hle.trans_lt hlowFace
  have hlowBp : (derivative B * c * d).natDegree < idx := by
    have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
      (natDegree_derivative_le B).trans (by omega)
    have hcd : (c * d).natDegree ≤ (4 * n - g) + (5 * n - h) :=
      natDegree_mul_le_of_le hc hd
    have hprod := natDegree_mul_le_of_le hdB hcd
    have hsum : (3 * n - g - 1) + ((4 * n - g) + (5 * n - h)) =
        12 * n - 2 * g - h - 1 := by omega
    have hle : (derivative B * (c * d)).natDegree ≤
        12 * n - 2 * g - h - 1 := by
      simpa only [hsum] using hprod
    have hassoc : derivative B * (c * d) = derivative B * c * d := by
      ring
    rw [hassoc] at hle
    exact hle.trans_lt hlowFace
  have hlowBe : (B ^ 2 * derivative e).natDegree < idx := by
    have hde : (derivative e).natDegree ≤ 6 * n - h - 1 :=
      (natDegree_derivative_le e).trans (by omega)
    have hprod := natDegree_mul_le_of_le hB2deg hde
    have hsum : (6 * n - 2 * g) + (6 * n - h - 1) =
        12 * n - 2 * g - h - 1 := by omega
    have hle : (B ^ 2 * derivative e).natDegree ≤
        12 * n - 2 * g - h - 1 := by
      simpa only [hsum] using hprod
    exact hle.trans_lt hlowFace
  have h0I3 : ((-9 / 4 : k) • (A * derivative I3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hI3low, mul_zero]
  have h0Ad2 : ((3 : k) • derivative (A * d ^ 2)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAd2, mul_zero]
  have h0ee : ((-18 : k) • (e * derivative e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hee, mul_zero]
  have h0Bcd : ((3 : k) • derivative (B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBcd, mul_zero]
  have h0Bp : ((6 : k) • (derivative B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBp, mul_zero]
  have h0Be : ((-3 : k) • (B ^ 2 * derivative e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBe, mul_zero]
  have hcast9 : (((12 * n - 3 * g : ℕ) : k)) = ((9 * n : ℕ) : k) := by
    congr 1
    omega
  have hcast3 : (((4 * n - g : ℕ) : k)) = ((3 * n : ℕ) : k) := by
    congr 1
    omega
  have hAB2csm : ((-2 : k) • derivative (A * B ^ 2 * c)).coeff idx =
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g) * ((9 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hAB2cder, hcast9]
  have hc3sm : ((6 : k) • (c ^ 2 * derivative c)).coeff idx =
      (6 : k) * (c.coeff (4 * n - g) ^ 3 * ((3 * n : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hc3, hcast3]
    ring
  have hinner : (residualRowOneInner68 A B c d e).coeff idx =
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
          c.coeff (4 * n - g) * ((9 * n : ℕ) : k)) +
        (6 : k) * (c.coeff (4 * n - g) ^ 3 * ((3 * n : ℕ) : k)) := by
    dsimp [residualRowOneInner68]
    simp only [coeff_add]
    rw [h0I3, h0Ad2, hAB2csm, hc3sm, h0Bcd, h0Bp, h0Be, h0ee]
    ring
  rw [residualRowOne_eq_inner68, coeff_smul, smul_eq_mul, hinner]

set_option maxHeartbeats 2000000 in
theorem residualRowOne_coeff_rightChamber_eq68_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      6 * n)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (-32 / 3 : k) * (n : k) * c.coeff (4 * n - g) ^ 3 := by
  rw [residualRowOne_coeff_rightChamber_of_alphaWall A B c d e n g h
    hn hg hgh hh hwall hright hA hB hcdeg hd he hI3]
  have hcast9 : (((9 * n : ℕ) : k)) = (9 : k) * (n : k) := by
    push_cast
    rfl
  have hcast3 : (((3 * n : ℕ) : k)) = (3 : k) * (n : k) := by
    push_cast
    rfl
  rw [hcast9, hcast3]
  exact alphaWallRowOneRightScalar68 (n : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g)) hdisc

theorem residualRowOne_right_coeff_ne_zero68_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      6 * n)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) ≠ 0 := by
  rw [residualRowOne_coeff_rightChamber_eq68_of_alphaWall A B c d e n g h
    hn hg hgh hh hwall hright hA hB hcdeg hd he hI3 hdisc]
  exact alphaWallRowOneRightScalar_ne_zero68 (n : k) (c.coeff (4 * n - g))
    (Nat.cast_ne_zero.mpr (by omega)) hc0

set_option maxHeartbeats 6000000 in
/-- On `2h=3g`, residual row one is the ordinary balanced cubic face;
I3 has already dropped below `7n`. -/
theorem residualRowOne_coeff_balancedChamber_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      6 * n) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (-4 / 27 : k) *
        (A.coeff (2 * n) *
            ((3 : k) * d.coeff (5 * n - h) ^ 2 -
              (2 : k) * B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) *
            ((12 * n - 3 * g : ℕ) : k) +
          (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 -
          (18 : k) * ((6 * n - h : ℕ) : k) *
            e.coeff (6 * n - h) ^ 2) := by
  let I3 := secondaryResidualInvariantThreePolynomial68 A B c d e
  set idx := 12 * n - 3 * g - 1
  have hI3low : (A * derivative I3).natDegree < idx := by
    have h := residual_natDegree_mul_derivative_le68 A I3 (2 * n) (6 * n)
      hA (by omega) hI3
    have hi : 2 * n + 6 * n - 1 = 8 * n - 1 := by omega
    have hle : (A * derivative I3).natDegree ≤ 8 * n - 1 := by
      simpa only [hi] using h
    have hlt : 8 * n - 1 < idx := by dsimp [idx]; omega
    exact hle.trans_lt hlt
  have hd2deg : (d ^ 2).natDegree ≤ 10 * n - 3 * g := by
    compute_degree
    omega
  have hd2 : (d ^ 2).coeff (10 * n - 3 * g) =
      d.coeff (5 * n - h) ^ 2 := by
    have hd2pow := coeff_pow_at_bound68 d (5 * n - h) 2 hd
    have hi : 2 * (5 * n - h) = 10 * n - 3 * g := by omega
    simpa only [hi] using hd2pow
  have hAd2coeff := coeff_mul_at_bounds68 A (d ^ 2) (2 * n) (10 * n - 3 * g)
    hA hd2deg
  have hiAd2 : 2 * n + (10 * n - 3 * g) = 12 * n - 3 * g := by omega
  rw [hiAd2, hd2] at hAd2coeff
  have hAd2der := coeff_derivative_at_bound68 (A * d ^ 2)
    (12 * n - 3 * g) (by omega)
  rw [hAd2coeff] at hAd2der
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have hB2pow := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using hB2pow
  have hAB2ccoeff := coeff_mul_mul_at_bounds68 A (B ^ 2) c
    (2 * n) (6 * n - 2 * g) (4 * n - g) hA hB2deg hc
  have hiAB2c : 2 * n + (6 * n - 2 * g) + (4 * n - g) = 12 * n - 3 * g :=
    by omega
  rw [hiAB2c, hB2] at hAB2ccoeff
  have hAB2cder := coeff_derivative_at_bound68 (A * B ^ 2 * c)
    (12 * n - 3 * g) (by omega)
  rw [hAB2ccoeff] at hAB2cder
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hc3 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (8 * n - 2 * g) (4 * n - g) (by omega) hc2deg hc
  have hic3 : (8 * n - 2 * g) + (4 * n - g) - 1 = idx := by
    dsimp [idx]; omega
  rw [hic3, hc2] at hc3
  have hee := coeff_mul_derivative_at_bounds68 e e
    (6 * n - h) (6 * n - h) (by omega) he he
  have hiee : (6 * n - h) + (6 * n - h) - 1 = 12 * n - 2 * h - 1 := by omega
  rw [hiee] at hee
  have hidx_ee : 12 * n - 2 * h - 1 = idx := by
    dsimp [idx]; omega
  have hlowFace : 12 * n - 2 * g - h - 1 < idx := by
    dsimp [idx]
    omega
  have hlowBcd : (derivative (B * c * d)).natDegree < idx := by
    have hBc : (B * c).natDegree ≤ (3 * n - g) + (4 * n - g) :=
      natDegree_mul_le_of_le hB hc
    have hprod := natDegree_mul_le_of_le hBc hd
    have hsum : (3 * n - g) + (4 * n - g) + (5 * n - h) =
        12 * n - 2 * g - h := by omega
    rw [hsum] at hprod
    have hder := natDegree_derivative_le (B * c * d)
    have hle : (derivative (B * c * d)).natDegree ≤
        12 * n - 2 * g - h - 1 := by omega
    exact hle.trans_lt hlowFace
  have hlowBp : (derivative B * c * d).natDegree < idx := by
    have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
      (natDegree_derivative_le B).trans (by omega)
    have hcd : (c * d).natDegree ≤ (4 * n - g) + (5 * n - h) :=
      natDegree_mul_le_of_le hc hd
    have hprod := natDegree_mul_le_of_le hdB hcd
    have hsum : (3 * n - g - 1) + ((4 * n - g) + (5 * n - h)) =
        12 * n - 2 * g - h - 1 := by omega
    have hle : (derivative B * (c * d)).natDegree ≤
        12 * n - 2 * g - h - 1 := by
      simpa only [hsum] using hprod
    have hassoc : derivative B * (c * d) = derivative B * c * d := by
      ring
    rw [hassoc] at hle
    exact hle.trans_lt hlowFace
  have hlowBe : (B ^ 2 * derivative e).natDegree < idx := by
    have hde : (derivative e).natDegree ≤ 6 * n - h - 1 :=
      (natDegree_derivative_le e).trans (by omega)
    have hprod := natDegree_mul_le_of_le hB2deg hde
    have hsum : (6 * n - 2 * g) + (6 * n - h - 1) =
        12 * n - 2 * g - h - 1 := by omega
    have hle : (B ^ 2 * derivative e).natDegree ≤
        12 * n - 2 * g - h - 1 := by
      simpa only [hsum] using hprod
    exact hle.trans_lt hlowFace
  have h0I3 : ((-9 / 4 : k) • (A * derivative I3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hI3low, mul_zero]
  have h0Bcd : ((3 : k) • derivative (B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBcd, mul_zero]
  have h0Bp : ((6 : k) • (derivative B * c * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBp, mul_zero]
  have h0Be : ((-3 : k) • (B ^ 2 * derivative e)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hlowBe, mul_zero]
  have hAd2sm : ((3 : k) • derivative (A * d ^ 2)).coeff idx =
      (3 : k) * (A.coeff (2 * n) * d.coeff (5 * n - h) ^ 2 *
        ((12 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hAd2der]
  have hAB2csm : ((-2 : k) • derivative (A * B ^ 2 * c)).coeff idx =
      (-2 : k) * (A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g) * ((12 * n - 3 * g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hAB2cder]
  have hc3sm : ((6 : k) • (c ^ 2 * derivative c)).coeff idx =
      (6 : k) * (c.coeff (4 * n - g) ^ 2 * c.coeff (4 * n - g) *
        ((4 * n - g : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, hc3]
  have heesm : ((-18 : k) • (e * derivative e)).coeff idx =
      (-18 : k) * (e.coeff (6 * n - h) ^ 2 * ((6 * n - h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul, ← hidx_ee, hee]
    ring
  have hinner : (residualRowOneInner68 A B c d e).coeff idx =
      A.coeff (2 * n) *
          ((3 : k) * d.coeff (5 * n - h) ^ 2 -
            (2 : k) * B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g)) *
          ((12 * n - 3 * g : ℕ) : k) +
        (6 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 -
        (18 : k) * ((6 * n - h : ℕ) : k) * e.coeff (6 * n - h) ^ 2 := by
    dsimp [residualRowOneInner68]
    simp only [coeff_add]
    rw [h0I3, hAd2sm, hAB2csm, hc3sm, h0Bcd, h0Bp, h0Be, heesm]
    ring
  rw [residualRowOne_eq_inner68, coeff_smul, smul_eq_mul, hinner]

set_option maxHeartbeats 2000000 in
theorem residualRowOne_coeff_balancedChamber_eq68_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      6 * n)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (-64 / 9 : k) * ((4 * n - g : ℕ) : k) * c.coeff (4 * n - g) ^ 3 := by
  rw [residualRowOne_coeff_balancedChamber_of_alphaWall A B c d e n g h
    hn hg hgh hh hwall hbalanced hA hB hcdeg hd he hI3]
  have hcast12 : (((12 * n - 3 * g : ℕ) : k)) =
      (12 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 12 * n)]
    push_cast
    rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) =
      (4 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - h : ℕ) : k)) =
      (6 : k) * (n : k) - (h : k) := by
    rw [Nat.cast_sub (by omega : h ≤ 6 * n)]
    push_cast
    rfl
  have hbal : (2 : k) * (h : k) = (3 : k) * (g : k) := by
    have := congrArg (fun m : ℕ => (m : k)) hbalanced
    push_cast at this
    exact this
  rw [hcast12, hcast4, hcast6]
  exact residualRowOneScalar68 (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hc0 hbal hdisc hinc hrel

theorem residualRowOne_balanced_coeff_ne_zero68_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      6 * n)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) ≠ 0 := by
  rw [residualRowOne_coeff_balancedChamber_eq68_of_alphaWall A B c d e n g h
    hn hg hgh hh hwall hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel]
  have hcast4 : (((4 * n - g : ℕ) : k)) =
      (4 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  rw [hcast4]
  have hNG : (4 : k) * (n : k) - (g : k) ≠ 0 := by
    have hnat : ((4 * n - g : ℕ) : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega)
    rwa [hcast4] at hnat
  exact residualRowOneScalar_ne_zero68 (n : k) (g : k) (h : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (e.coeff (6 * n - h)) hc0 hNG
    (by
      have := congrArg (fun m : ℕ => (m : k)) hbalanced
      push_cast at this
      exact this)
    hdisc hinc hrel

/-! ## Chamber contradictions on a middle residual gap -/

set_option maxHeartbeats 4000000 in
/-- On `2h<3g`, `Q` of degree `≤ 6n` still lies strictly below the left
index, so the ordinary `d e` coefficient survives. -/
theorem residualRowTwo_coeff_leftChamber_of_Qle_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) =
      (8 / 3 : k) * ((11 * n - 2 * h : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 2 * h - 1
  have hcubic : 8 * n - 1 < idx := by
    dsimp [idx]
    omega
  have hAQ : (A * derivative Q).natDegree < idx := by
    have h := residual_natDegree_mul_derivative_le68 A Q (2 * n) (6 * n)
      hA (by omega) hQ
    have hi : 2 * n + 6 * n - 1 = 8 * n - 1 := by omega
    have hle : (A * derivative Q).natDegree ≤ 8 * n - 1 := by
      simpa only [hi] using h
    exact hle.trans_lt hcubic
  have hAQ' : (derivative A * Q).natDegree < idx := by
    have h := residual_natDegree_derivative_mul_le68 A Q (2 * n) (6 * n)
      (by omega) hA hQ
    have hi : 2 * n + 6 * n - 1 = 8 * n - 1 := by omega
    have hle : (derivative A * Q).natDegree ≤ 8 * n - 1 := by
      simpa only [hi] using h
    exact hle.trans_lt hcubic
  have hcore := residualRowTwoInner_BcCore_degree_le68_of_alphaWall A B c n g
    hg hwall hA hB hc
  have hAB : (A * B ^ 2 * derivative B).natDegree < idx :=
    hcore.1.trans_lt (by dsimp [idx]; omega)
  have hA3 : (derivative A * B ^ 3).natDegree < idx :=
    hcore.2.1.trans_lt (by dsimp [idx]; omega)
  have hBc : (derivative (B * c ^ 2)).natDegree < idx :=
    hcore.2.2.trans_lt (by dsimp [idx]; omega)
  have hBd := residualRowTwoInner_Bd_degree_le68_of_alphaWall B d n g h
    hg hgh hh hwall hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hide : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h) hd he
  rw [hide] at hdecoeff
  have hder0 : 0 < 11 * n - 2 * h := by omega
  have hde := coeff_derivative_at_bound68 (d * e) (11 * n - 2 * h) hder0
  rw [hdecoeff] at hde
  have h0Q : ((-6 : k) • (A * derivative Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ, mul_zero]
  have h0Q' : ((3 : k) • (derivative A * Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ', mul_zero]
  have h0AB : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAB, mul_zero]
  have h0A3 : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hA3, mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have h0Bc : ((6 : k) • derivative (B * c ^ 2)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBc, mul_zero]
  have hde' : ((-18 : k) • derivative (d * e)).coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hde]
  have hinner : inner.coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0AB, h0A3, h0Bd, h0Bc, hde']
    ring
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  ring

theorem residualRowTwo_leftChamber_ne_zero_of_Qle_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) ≠ 0 := by
  rw [residualRowTwo_coeff_leftChamber_of_Qle_of_alphaWall A B c d e n g h
    hn hg hgh hh hwall hleft hA hB hc hd he hQ]
  have hscalar : (8 / 3 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 2 * h : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hscalar hN) hd0) he0

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_not_leftChamber68_of_alphaWall_of_Qle
    (A B c d e load : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hleft : 2 * h < 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 6 * n)
    (hload : load.natDegree ≤ 11 * n - 3 * g - 1)
    (hsum : secondaryResidualRowTwoPolynomial68 A B c d e + load = 0)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    False := by
  have hidx : 11 * n - 3 * g - 1 < 11 * n - 2 * h - 1 := by omega
  have hload' : load.natDegree < 11 * n - 2 * h - 1 :=
    hload.trans_lt hidx
  have hcoeff0 := residualRowTwo_coeff_eq_zero_of_loadCutoff68_of_alphaWall
    A B c d e load (11 * n - 2 * h - 1) hload' hsum
  exact residualRowTwo_leftChamber_ne_zero_of_Qle_of_alphaWall A B c d e n g h
    hn hg hgh hh hwall hleft hA hB hc hd he hQ hd0 he0 hcoeff0

theorem residualRowOne_not_rightChamber68_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hright : 3 * g < 2 * h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      6 * n)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hrow : (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) = 0) :
    False :=
  residualRowOne_right_coeff_ne_zero68_of_alphaWall A B c d e n g h
    hn hg hgh hh hwall hright hA hB hcdeg hd he hI3 hdisc hc0 hrow

theorem residualRowOne_not_balancedChamber68_of_alphaWall
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hwall : g = n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hcdeg : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hI3 : (secondaryResidualInvariantThreePolynomial68 A B c d e).natDegree ≤
      6 * n)
    (hc0 : c.coeff (4 * n - g) ≠ 0)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hinc : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0)
    (hrel : (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0)
    (hrow : (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) = 0) :
    False :=
  residualRowOne_balanced_coeff_ne_zero68_of_alphaWall A B c d e n g h
    hn hg hgh hh hwall hbalanced hA hB hcdeg hd he hI3 hc0 hdisc hinc hrel hrow

/-! ## Canonical expanded transport: middle window is empty -/

set_option maxHeartbeats 8000000 in
/-- On the canonical expanded system, after `l = 0` on `g = n`, every
non-balanced middle residual window is empty.  Left is the ordinary
`de` face strictly above the cubic load; right is killed by load-free
row one after the I3 drop.  The remaining middle fibre is `2h = 3g`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_alphaWallMixedMiddleImpossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (h : ℕ) (hterminal : terminal ≠ 0)
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
      g = n)
    (hgh :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g < h)
    (hh :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      h < 2 * g)
    (hmiddle :
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
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h)
    (hattained :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0)
    (hnotbal :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * h ≠ 3 * g) :
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
  change g = n at hwall
  change g < h at hgh
  change h < 2 * g at hh
  change d.natDegree ≤ 5 * n - h ∧
    ee.natDegree ≤ 6 * n - h at hmiddle
  change d.coeff (5 * n - h) ≠ 0 ∨
    ee.coeff (6 * n - h) ≠ 0 at hattained
  change 2 * h ≠ 3 * g at hnotbal
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_alphaWallClassified68_of_wall
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
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
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
  have hD : De.natDegree ≤ 5 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.1
  have he0 : ee.natDegree ≤ 6 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.1
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hboundary :=
    maximalExpandedIntegratedPolynomialLowerSystem_alphaWallBoundary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) at hboundary
  have hsupport : Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 :=
    hboundary.2.2.2
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
  have hface :=
    maximalExpandedIntegratedPolynomialLowerSystem_alphaWallResidualMiddleFace68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E h
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgh)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hh)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hmiddle)
  change l = 0 ∧
    SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h)) at hface
  have hclassif := secondaryResidualBetweenFace68_classify_of_support
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g)) (ce.coeff (4 * n - g))
    (d.coeff (5 * n - h)) (ee.coeff (6 * n - h))
    ha hsupport hattained hface.2
  have hc0 : ce.coeff (4 * n - g) ≠ 0 := hclassif.2.1
  have hd0 : d.coeff (5 * n - h) ≠ 0 := hclassif.2.2.1
  have hee0 : ee.coeff (6 * n - h) ≠ 0 := hclassif.2.2.2.1
  have hdisc :
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        (3 : k) * ce.coeff (4 * n - g) ^ 2 = 0 := hclassif.2.2.2.2
  have hd_le : d.natDegree ≤ 5 * n - g := by omega
  have hQdeg :
      (residualIncidenceQ68 Be ce d ee).natDegree ≤ 6 * n :=
    residualIncidenceQ68_degree_le_sixRadius_of_alphaWall
      beta gamma delta epsilon zeta i4 Ae Be ce d ee n g hwall
      hA hB hc hd_le he0 hi4c
  have hI3deg :
      (secondaryResidualInvariantThreePolynomial68 Ae Be ce d ee).natDegree ≤
        6 * n :=
    secondaryResidualInvariantThreePolynomial68_degree_le_sixRadius_of_alphaWall
      beta gamma delta epsilon zeta i3 Ae Be ce d ee n g hwall
      hA hB hc hd_le he0 hi3c
  have hrow1 :=
    maximalExpandedIntegratedPolynomialLowerSystem_alphaWallRowOneCubicFace68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧
    (secondaryResidualRowOnePolynomial68 Ae Be ce d ee).coeff
        (12 * n - 3 * g - 1) = 0 at hrow1
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at h2e
  have hres := cubicRowTwoPolynomial68_residualSplit
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee
  have hsum :
      secondaryResidualRowTwoPolynomial68 Ae Be ce d ee +
        cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
    simpa using hres.symm.trans h2e
  have hloaddeg := cubicLoadRowTwoPolynomial68_degree_le_cubicFace_of_alphaWall
    l alpha beta gamma delta epsilon zeta eta Ae Be ce De ee n g
    hn hg hl hwall hA hB hc hD he0
  rcases lt_trichotomy (2 * h) (3 * g) with hleft | hbal | hright
  · exact residualRowTwo_not_leftChamber68_of_alphaWall_of_Qle
      Ae Be ce d ee
      (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee)
      n g h hn hg hgh hh hwall hleft hA hB hc hmiddle.1 hmiddle.2
      hQdeg (by simpa only [← hDrec] using hloaddeg) hsum hd0 hee0
  · exact (hnotbal hbal).elim
  · exact residualRowOne_not_rightChamber68_of_alphaWall
      Ae Be ce d ee n g h hn hg hgh hh hwall hright hA hB hc
      hmiddle.1 hmiddle.2 hI3deg hdisc hc0 hrow1.2

/-- On the canonical expanded system, after `l = 0` on `g = n`, a middle
residual gap that is not the balanced wall `2h = 3g` is impossible. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_alphaWallMixedEndgame68
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
      g = n)
    (hmiddle :
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
      let h := secondaryResidualGap68 n d ee
      g < h ∧ h < 2 * g ∧ 2 * h ≠ 3 * g) :
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
  let h := secondaryResidualGap68 n d ee
  change g = n at hwall
  change g < h ∧ h < 2 * g ∧ 2 * h ≠ 3 * g at hmiddle
  have hgap :=
    maximalExpandedIntegratedPolynomialLowerSystem_alphaWallResidualGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
    d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
    g < h ∧
    d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h at hgap
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hz : ¬ (d = 0 ∧ ee = 0) := by
    intro hboth
    have hgaph : h = 6 * n + 1 := by
      simp [h, secondaryResidualGap68, polynomialGap68, hboth.1, hboth.2]
    have : h < 2 * g := hmiddle.2.1
    omega
  have hattained :=
    secondaryResidualGap68_boundary_attained n d ee hdbase hebase hz
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_alphaWallMixedMiddleImpossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E h
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, h] using hmiddle.1)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, h] using hmiddle.2.1)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
        hgap.2.2.2.2.2)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hattained)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, h] using hmiddle.2.2)

#print axioms residualIncidenceQ68_coeff_sixRadius_of_alphaWall
#print axioms residualRowOne_coeff_rightChamber_eq68_of_alphaWall
#print axioms residualRowOne_not_rightChamber68_of_alphaWall
#print axioms residualRowTwo_not_leftChamber68_of_alphaWall_of_Qle
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_alphaWallMixedEndgame68

end AlphaWallMixedEndgame68

end Max11DegreeRoutes
