import LowScale68SecondaryLaterDeepFiveRadiusResidualEndgame
import LowScale68SecondaryResidualRowTwoBalanced

/-! # Scalar faces of the reduced row on `2g = 5n`

The reduced row has four pieces: a fixed `B,c` face, the moving `d*e`
face, a strictly lower tail, and the `zeta` face at degree `4n-1`.  Their
only possible ties are `2h=7n` (`d*e` against `zeta`) and `2h=3g`
(`d*e` against the fixed core).
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveRadiusScalarFaces68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Fixed `B,c` cubic face of reduced row two. -/
def fiveRadiusRowTwoFixedCore68 (A B c : k[X]) : k[X] :=
  (-4 / 27 : k) •
    ((-2 : k) • (A * B ^ 2 * derivative B) +
      (-2 / 3 : k) • (derivative A * B ^ 3) +
      (6 : k) • derivative (B * c ^ 2))

/-- Terms strictly below the fixed cubic face throughout `g<h<5n`. -/
def fiveRadiusRowTwoTail68
    (gamma epsilon i4 : k) (A B c d : k[X]) : k[X] :=
  (-8 / 9 : k) • derivative (B ^ 2 * d) -
    (1 / 6 * i4 : k) • derivative A -
    (4 / 3 * gamma : k) • derivative (B * c) +
    (2 * epsilon : k) • derivative d

set_option maxHeartbeats 4000000 in
theorem fiveRadiusReducedRowTwoPolynomial68_faceSplit
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) :
    fiveRadiusReducedRowTwoPolynomial68 gamma epsilon zeta i4 A B c d e =
      fiveRadiusRowTwoFixedCore68 A B c +
        (8 / 3 : k) • derivative (d * e) +
        fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d +
        zeta • derivative ((1 / 4 : k) • A ^ 2 + c) := by
  simp only [fiveRadiusReducedRowTwoPolynomial68,
    fiveRadiusRowTwoFixedCore68, fiveRadiusRowTwoTail68]
  module

set_option maxHeartbeats 4000000 in
theorem fiveRadiusRowTwoTail68_degree_lt_fixedFace
    (gamma epsilon i4 : k) (A B c d : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (hgh : g < h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d).natDegree <
      11 * n - 3 * g - 1 := by
  let bound := 11 * n - 3 * g - 1
  have hBdprod : (B ^ 2 * d).natDegree ≤
      (6 * n - 2 * g) + (5 * n - h) := by
    compute_degree
    omega
  have hBdder := natDegree_derivative_le (B ^ 2 * d)
  have hBd : (derivative (B ^ 2 * d)).natDegree < bound := by
    dsimp [bound]
    omega
  have hA' : (derivative A).natDegree < bound := by
    dsimp [bound]
    compute_degree
    omega
  have hBcprod : (B * c).natDegree ≤
      (3 * n - g) + (4 * n - g) := by
    compute_degree
    omega
  have hBcder := natDegree_derivative_le (B * c)
  have hBc : (derivative (B * c)).natDegree < bound := by
    dsimp [bound]
    omega
  have hd' : (derivative d).natDegree < bound := by
    dsimp [bound]
    compute_degree
    omega
  have h1 := deepGap_natDegree_smul_lt68 (-8 / 9 : k) hBd
  have h2 := deepGap_natDegree_smul_lt68 (1 / 6 * i4 : k) hA'
  have h3 := deepGap_natDegree_smul_lt68 (4 / 3 * gamma : k) hBc
  have h4 := deepGap_natDegree_smul_lt68 (2 * epsilon : k) hd'
  simp only [fiveRadiusRowTwoTail68]
  exact deepGap_natDegree_add_lt
    (deepGap_natDegree_sub_lt (deepGap_natDegree_sub_lt h1 h2) h3) h4

set_option maxHeartbeats 4000000 in
theorem fiveRadiusRowTwoFixedCore68_degree_le
    (A B c : k[X]) (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (fiveRadiusRowTwoFixedCore68 A B c).natDegree ≤
      11 * n - 3 * g - 1 := by
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
    (natDegree_derivative_le B).trans (by omega)
  have hAB2 := natDegree_mul_le_of_le hA hB2
  have h1 : (A * B ^ 2 * derivative B).natDegree ≤
      11 * n - 3 * g - 1 := by
    have := natDegree_mul_le_of_le hAB2 hdB
    omega
  have hB3 : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
    (natDegree_derivative_le A).trans (by omega)
  have h2 : (derivative A * B ^ 3).natDegree ≤
      11 * n - 3 * g - 1 := by
    have := natDegree_mul_le_of_le hdA hB3
    omega
  have hc2 : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hBc : (B * c ^ 2).natDegree ≤ 11 * n - 3 * g := by
    have := natDegree_mul_le_of_le hB hc2
    omega
  have h3 : (derivative (B * c ^ 2)).natDegree ≤
      11 * n - 3 * g - 1 :=
    (natDegree_derivative_le _).trans (by omega)
  have h1s : ((-2 : k) • (A * B ^ 2 * derivative B)).natDegree ≤
      11 * n - 3 * g - 1 := (natDegree_smul_le _ _).trans h1
  have h2s : ((-2 / 3 : k) • (derivative A * B ^ 3)).natDegree ≤
      11 * n - 3 * g - 1 := (natDegree_smul_le _ _).trans h2
  have h3s : ((6 : k) • derivative (B * c ^ 2)).natDegree ≤
      11 * n - 3 * g - 1 := (natDegree_smul_le _ _).trans h3
  have hadd1 : (((-2 : k) • (A * B ^ 2 * derivative B)) +
      (-2 / 3 : k) • (derivative A * B ^ 3)).natDegree ≤
      11 * n - 3 * g - 1 :=
    (natDegree_add_le _ _).trans (max_le h1s h2s)
  have hadd2 : (((-2 : k) • (A * B ^ 2 * derivative B)) +
      (-2 / 3 : k) • (derivative A * B ^ 3) +
      (6 : k) • derivative (B * c ^ 2)).natDegree ≤
      11 * n - 3 * g - 1 :=
    (natDegree_add_le _ _).trans (max_le hadd1 h3s)
  simp only [fiveRadiusRowTwoFixedCore68]
  exact (natDegree_smul_le _ _).trans hadd2

set_option maxHeartbeats 6000000 in
theorem fiveRadiusRowTwoFixedCore68_coeff
    (A B c : k[X]) (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (fiveRadiusRowTwoFixedCore68 A B c).coeff (11 * n - 3 * g - 1) =
      (32 / 81 : k) * ((11 * n - 3 * g : ℕ) : k) *
        A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 := by
  set idx := 11 * n - 3 * g - 1
  change (fiveRadiusRowTwoFixedCore68 A B c).coeff idx = _
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
  have hA3 := coeff_mul_derivative_at_bounds68 (B ^ 3) A
    (9 * n - 3 * g) (2 * n) (by omega) hB3deg hA
  have hiA3 : (9 * n - 3 * g) + 2 * n - 1 = idx := by
    dsimp [idx]
    omega
  rw [hiA3, hB3] at hA3
  have hA3' : (derivative A * B ^ 3).coeff idx =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 *
        ((2 * n : ℕ) : k) := by
    rw [show (derivative A * B ^ 3).coeff idx =
        (B ^ 3 * derivative A).coeff idx by
      congr 1
      ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hA3
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have hBccoeff := coeff_mul_at_bounds68 B (c ^ 2)
    (3 * n - g) (8 * n - 2 * g) hB hc2deg
  have hiBc : (3 * n - g) + (8 * n - 2 * g) = 11 * n - 3 * g := by omega
  rw [hiBc, hc2] at hBccoeff
  have hBc := coeff_derivative_at_bound68 (B * c ^ 2)
    (11 * n - 3 * g) (by omega)
  rw [hBccoeff] at hBc
  have hcast3 : (((3 * n - g : ℕ) : k)) =
      (3 : k) * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast2 : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    push_cast
    rfl
  have hcast11 : (((11 * n - 3 * g : ℕ) : k)) =
      (11 : k) * (n : k) - (3 : k) * (g : k) := by
    rw [Nat.cast_sub (by omega : 3 * g ≤ 11 * n)]
    push_cast
    rfl
  simp only [fiveRadiusRowTwoFixedCore68, coeff_smul, coeff_add,
    smul_eq_mul, hABpow, hA3', hBc, hcast3, hcast2, hcast11, idx]
  have hsc := residualRowTwoRightCoreScalar68_of_disc (n : k) (g : k)
    (A.coeff (2 * n)) (B.coeff (3 * n - g)) (c.coeff (4 * n - g)) hdisc
  linear_combination (-4 / 27 : k) * hsc

set_option maxHeartbeats 3000000 in
theorem fiveRadiusRowTwoDE68_coeff
    (d e : k[X]) (n h : ℕ) (hn : 0 < n) (hh : h < 5 * n)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    ((8 / 3 : k) • derivative (d * e)).coeff (11 * n - 2 * h - 1) =
      (8 / 3 : k) * ((11 * n - 2 * h : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
  have hdecoeff := coeff_mul_at_bounds68 d e
    (5 * n - h) (6 * n - h) hd he
  have hide : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  rw [hide] at hdecoeff
  have hder := coeff_derivative_at_bound68 (d * e)
    (11 * n - 2 * h) (by omega)
  rw [hdecoeff] at hder
  rw [coeff_smul, smul_eq_mul, hder]
  ring

set_option maxHeartbeats 2000000 in
theorem derivative_quarterSquare_add_degree_le_zeta68
    (A c : k[X]) (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n) (hc : c.natDegree ≤ 4 * n - g) :
    (derivative ((1 / 4 : k) • A ^ 2 + c)).natDegree ≤ 4 * n - 1 := by
  have hP : ((1 / 4 : k) • A ^ 2 + c).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hder := natDegree_derivative_le ((1 / 4 : k) • A ^ 2 + c)
  omega

set_option maxHeartbeats 5000000 in
/-- Exact `d*e/zeta` coefficient on their wall `2h=7n`. -/
theorem fiveRadiusReducedRowTwo_coeff_zetaDEWall68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (hgh : g < h)
    (hh : h < 5 * n) (htie : 2 * h = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusReducedRowTwoPolynomial68 gamma epsilon zeta i4 A B c d e).coeff
        (4 * n - 1) =
      (8 / 3 : k) * ((4 * n : ℕ) : k) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) +
        zeta * (n : k) * A.coeff (2 * n) ^ 2 := by
  have hcore := fiveRadiusRowTwoFixedCore68_degree_le A B c n g hn hwall hA hB hc
  have hcore' : (fiveRadiusRowTwoFixedCore68 A B c).natDegree < 4 * n - 1 := by
    omega
  have htail := fiveRadiusRowTwoTail68_degree_lt_fixedFace
    gamma epsilon i4 A B c d n g h hn hwall hgh hA hB hc hd
  have htail' : (fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d).natDegree <
      4 * n - 1 := htail.trans (by omega)
  have hde := fiveRadiusRowTwoDE68_coeff d e n h hn hh hd he
  have hdei : 11 * n - 2 * h - 1 = 4 * n - 1 := by omega
  have hdeM : 11 * n - 2 * h = 4 * n := by omega
  rw [hdei, hdeM] at hde
  have hz := derivative_quarterSquare_add_coeff_zetaWall68
    A c n g hn hwall hA hc
  rw [fiveRadiusReducedRowTwoPolynomial68_faceSplit, coeff_add, coeff_add,
    coeff_add, coeff_eq_zero_of_natDegree_lt hcore',
    coeff_eq_zero_of_natDegree_lt htail', zero_add, hde,
    coeff_smul, smul_eq_mul, hz]
  ring

set_option maxHeartbeats 5000000 in
/-- Above the `d*e/zeta` comparison, the unique degree `4n-1` term kills
`zeta`. -/
theorem fiveRadiusReducedRowTwo_forces_zeta_aboveDE68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (hgh : g < h)
    (hh : h < 5 * n) (habove : 7 * n < 2 * h)
    (ha : A.coeff (2 * n) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hrow : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 A B c d e = 0) :
    zeta = 0 := by
  have hcore := fiveRadiusRowTwoFixedCore68_degree_le A B c n g hn hwall hA hB hc
  have hcore' : (fiveRadiusRowTwoFixedCore68 A B c).natDegree < 4 * n - 1 := by
    omega
  have htail := fiveRadiusRowTwoTail68_degree_lt_fixedFace
    gamma epsilon i4 A B c d n g h hn hwall hgh hA hB hc hd
  have htail' : (fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d).natDegree <
      4 * n - 1 := htail.trans (by omega)
  have hdeprod : (d * e).natDegree ≤
      (5 * n - h) + (6 * n - h) := by
    compute_degree
    omega
  have hdeder := natDegree_derivative_le (d * e)
  have hde : ((8 / 3 : k) • derivative (d * e)).natDegree < 4 * n - 1 := by
    apply (natDegree_smul_le _ _).trans_lt
    omega
  have hz := derivative_quarterSquare_add_coeff_zetaWall68
    A c n g hn hwall hA hc
  have hcoeff := congrArg (fun p : k[X] => p.coeff (4 * n - 1)) hrow
  rw [fiveRadiusReducedRowTwoPolynomial68_faceSplit, coeff_add, coeff_add,
    coeff_add, coeff_eq_zero_of_natDegree_lt hcore',
    coeff_eq_zero_of_natDegree_lt hde,
    coeff_eq_zero_of_natDegree_lt htail', coeff_smul, smul_eq_mul,
    hz, coeff_zero, zero_add] at hcoeff
  simp only [zero_add] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_right
    (mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (pow_ne_zero 2 ha))

set_option maxHeartbeats 5000000 in
theorem fiveRadiusReducedRowTwo_DE_ne_zero_of_left68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (hgh : g < h)
    (hh : h < 5 * n) (hleft : 2 * h < 3 * g)
    (hzeta : zeta = 0 ∨ 2 * h < 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    (fiveRadiusReducedRowTwoPolynomial68 gamma epsilon zeta i4 A B c d e).coeff
        (11 * n - 2 * h - 1) ≠ 0 := by
  have hcore := fiveRadiusRowTwoFixedCore68_degree_le A B c n g hn hwall hA hB hc
  have hcore' : (fiveRadiusRowTwoFixedCore68 A B c).natDegree <
      11 * n - 2 * h - 1 := hcore.trans_lt (by omega)
  have htail := fiveRadiusRowTwoTail68_degree_lt_fixedFace
    gamma epsilon i4 A B c d n g h hn hwall hgh hA hB hc hd
  have htail' : (fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d).natDegree <
      11 * n - 2 * h - 1 := htail.trans (by omega)
  have hzdeg := derivative_quarterSquare_add_degree_le_zeta68
    A c n g hn hwall hA hc
  have hz : (zeta • derivative ((1 / 4 : k) • A ^ 2 + c)).natDegree <
      11 * n - 2 * h - 1 := by
    rcases hzeta with hzeta | hbelow
    · rw [hzeta]
      simp only [zero_smul, natDegree_zero]
      omega
    · exact (natDegree_smul_le _ _).trans_lt (by omega)
  have hde := fiveRadiusRowTwoDE68_coeff d e n h hn hh hd he
  rw [fiveRadiusReducedRowTwoPolynomial68_faceSplit, coeff_add, coeff_add,
    coeff_add, coeff_eq_zero_of_natDegree_lt hcore',
    coeff_eq_zero_of_natDegree_lt htail',
    coeff_eq_zero_of_natDegree_lt hz, zero_add, add_zero, hde]
  have hscalar : (8 / 3 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 2 * h : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  simpa only [add_zero] using
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hscalar hN) hd0) he0)

set_option maxHeartbeats 6000000 in
theorem fiveRadiusReducedRowTwo_BC_ne_zero_of_right68
    (gamma epsilon i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (hgh : g < h)
    (hh : h < 5 * n) (hright : 3 * g < 2 * h)
    (ha : A.coeff (2 * n) ≠ 0)
    (hb : B.coeff (3 * n - g) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    (fiveRadiusReducedRowTwoPolynomial68 gamma epsilon 0 i4 A B c d e).coeff
        (11 * n - 3 * g - 1) ≠ 0 := by
  have htail := fiveRadiusRowTwoTail68_degree_lt_fixedFace
    gamma epsilon i4 A B c d n g h hn hwall hgh hA hB hc hd
  have hdeprod : (d * e).natDegree ≤
      (5 * n - h) + (6 * n - h) := by
    compute_degree
    omega
  have hdeder := natDegree_derivative_le (d * e)
  have hde : ((8 / 3 : k) • derivative (d * e)).natDegree <
      11 * n - 3 * g - 1 := by
    apply (natDegree_smul_le _ _).trans_lt
    omega
  have hcore := fiveRadiusRowTwoFixedCore68_coeff A B c n g hn
    hwall hA hB hc hdisc
  rw [fiveRadiusReducedRowTwoPolynomial68_faceSplit, zero_smul, add_zero,
    coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt hde,
    coeff_eq_zero_of_natDegree_lt htail, add_zero, hcore]
  have hscalar : (32 / 81 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 3 * g : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  simpa only [add_zero] using
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hscalar hN) ha)
      (pow_ne_zero 3 hb))

set_option maxHeartbeats 6000000 in
theorem fiveRadiusReducedRowTwo_balancedRelation68
    (gamma epsilon i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (hgh : g < h)
    (hh : h < 5 * n) (hbalanced : 2 * h = 3 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hrow : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon 0 i4 A B c d e = 0) :
    (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
      (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0 := by
  have htail := fiveRadiusRowTwoTail68_degree_lt_fixedFace
    gamma epsilon i4 A B c d n g h hn hwall hgh hA hB hc hd
  have hcore := fiveRadiusRowTwoFixedCore68_coeff A B c n g hn
    hwall hA hB hc hdisc
  have hde := fiveRadiusRowTwoDE68_coeff d e n h hn hh hd he
  have hidx : 11 * n - 2 * h - 1 = 11 * n - 3 * g - 1 := by omega
  have hM : 11 * n - 2 * h = 11 * n - 3 * g := by omega
  rw [hidx, hM] at hde
  have hcoeff := congrArg (fun p : k[X] => p.coeff (11 * n - 3 * g - 1)) hrow
  rw [fiveRadiusReducedRowTwoPolynomial68_faceSplit, zero_smul, add_zero,
    coeff_add, coeff_add, coeff_eq_zero_of_natDegree_lt htail, add_zero,
    hcore, hde, coeff_zero] at hcoeff
  have hfactor : (-8 / 27 : k) * ((11 * n - 3 * g : ℕ) : k) ≠ 0 :=
    mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (by omega))
  have hrewrite :
      (32 / 81 : k) * ((11 * n - 3 * g : ℕ) : k) *
          A.coeff (2 * n) * B.coeff (3 * n - g) ^ 3 +
        (8 / 3 : k) * ((11 * n - 3 * g : ℕ) : k) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) =
      (-8 / 27 : k) * ((11 * n - 3 * g : ℕ) : k) *
        ((4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
          (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)) := by
    linear_combination
      hdisc * ((32 / 81 : k) * ((11 * n - 3 * g : ℕ) : k) *
        B.coeff (3 * n - g))
  rw [hrewrite] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

/-- The two exact scalar walls left after all strict faces are eliminated. -/
structure FiveRadiusScalarSelector68
    (zeta : k) (A B c d e : k[X]) (n g h : ℕ) : Prop where
  cases :
    (2 * h = 7 * n ∧
      (8 / 3 : k) * ((4 * n : ℕ) : k) *
          d.coeff (5 * n - h) * e.coeff (6 * n - h) +
        zeta * (n : k) * A.coeff (2 * n) ^ 2 = 0) ∨
    (2 * h = 3 * g ∧ zeta = 0 ∧
      (4 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2 -
        (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h) = 0)

set_option maxHeartbeats 10000000 in
theorem fiveRadiusResidualEndgamePacket_scalarSelector68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hwall : 2 * g = 5 * n) (hgh : g < h)
    (hh : h < 5 * n) (ha : A.coeff (2 * n) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (P : FiveRadiusResidualEndgamePacket68
      gamma epsilon zeta i4 A B c d e n g h) :
    FiveRadiusScalarSelector68 zeta A B c d e n g h := by
  constructor
  rcases lt_trichotomy (2 * h) (7 * n) with hbelow | hwall7 | habove7
  · have hleft : 2 * h < 3 * g := by omega
    have hne := fiveRadiusReducedRowTwo_DE_ne_zero_of_left68
      gamma epsilon zeta i4 A B c d e n g h hn hwall hgh hh hleft
      (Or.inr hbelow) hA hB hc hd he P.d_ne P.e_ne
    have hz := congrArg (fun p : k[X] =>
      p.coeff (11 * n - 2 * h - 1)) P.row_two
    simp only [coeff_zero] at hz
    exact (hne hz).elim
  · left
    have hcoeff := congrArg (fun p : k[X] => p.coeff (4 * n - 1)) P.row_two
    rw [fiveRadiusReducedRowTwo_coeff_zetaDEWall68
      gamma epsilon zeta i4 A B c d e n g h hn hwall hgh hh hwall7
      hA hB hc hd he, coeff_zero] at hcoeff
    exact ⟨hwall7, hcoeff⟩
  · have hzeta := fiveRadiusReducedRowTwo_forces_zeta_aboveDE68
      gamma epsilon zeta i4 A B c d e n g h hn hwall hgh hh habove7 ha
      hA hB hc hd he P.row_two
    rcases lt_trichotomy (2 * h) (3 * g) with hleft | hbalanced | hright
    · have hne := fiveRadiusReducedRowTwo_DE_ne_zero_of_left68
        gamma epsilon zeta i4 A B c d e n g h hn hwall hgh hh hleft
        (Or.inl hzeta) hA hB hc hd he P.d_ne P.e_ne
      have hz := congrArg (fun p : k[X] =>
        p.coeff (11 * n - 2 * h - 1)) P.row_two
      simp only [coeff_zero] at hz
      exact (hne hz).elim
    · right
      have hrel := fiveRadiusReducedRowTwo_balancedRelation68
        gamma epsilon i4 A B c d e n g h hn hwall hgh hh hbalanced
        hA hB hc hd he P.discriminant (by simpa only [hzeta] using P.row_two)
      exact ⟨hbalanced, hzeta, hrel⟩
    · have hne := fiveRadiusReducedRowTwo_BC_ne_zero_of_right68
        gamma epsilon i4 A B c d e n g h hn hwall hgh hh hright ha P.b_ne
        hA hB hc hd he P.discriminant
      have hz := congrArg (fun p : k[X] =>
        p.coeff (11 * n - 3 * g - 1)) P.row_two
      simp only [hzeta, coeff_zero] at hz
      exact (hne hz).elim

set_option maxHeartbeats 24000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusScalarFaces68
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
      2 * g = 5 * n) :
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
    l = 0 ∧ beta = 0 ∧ delta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      ((d = 0 ∧ ee = 0) ∨
        (h < 5 * n ∧ ∃ i4 : k,
          FiveRadiusResidualEndgamePacket68 gamma epsilon zeta i4
            Ae Be ce d ee n g h ∧
          FiveRadiusScalarSelector68 zeta Ae Be ce d ee n g h) ∨
        (5 * n ≤ h ∧
          (d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0))) := by
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
  have old :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusResidualEndgame68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hwall
  change l = 0 ∧ beta = 0 ∧ delta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧ _ at old
  refine ⟨old.1, old.2.1, old.2.2.1, old.2.2.2.1,
    old.2.2.2.2.1, old.2.2.2.2.2.1, old.2.2.2.2.2.2.1, ?_⟩
  rcases old.2.2.2.2.2.2.2 with hzero | hlt | hge
  · exact Or.inl hzero
  · right; left
    rcases hlt with ⟨hlt, i4, P⟩
    have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
      ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
      ee.natDegree ≤ 6 * n - g ∧ _ at secondary
    have hn : 0 < n := by simpa only [n] using core.1
    have ha : Ae.coeff (2 * n) ≠ 0 := by
      simpa only [n, Ae] using core.2.2.2.2.2
    have hA : Ae.natDegree ≤ 2 * n := by
      have hAe : Ae.natDegree = 2 * n := by
        simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
      omega
    have hwall' : 2 * g = 5 * n := by
      simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall
    have selector := fiveRadiusResidualEndgamePacket_scalarSelector68
      gamma epsilon zeta i4 Ae Be ce d ee n g h hn hwall' old.2.2.2.1
      hlt ha hA secondary.2.1 secondary.2.2.1
      old.2.2.2.2.1 old.2.2.2.2.2.1 P
    exact ⟨hlt, i4, P, selector⟩
  · exact Or.inr (Or.inr hge)

#print axioms fiveRadiusReducedRowTwoPolynomial68_faceSplit
#print axioms fiveRadiusRowTwoFixedCore68_coeff
#print axioms fiveRadiusReducedRowTwo_coeff_zetaDEWall68
#print axioms fiveRadiusReducedRowTwo_forces_zeta_aboveDE68
#print axioms fiveRadiusReducedRowTwo_balancedRelation68
#print axioms FiveRadiusScalarSelector68
#print axioms fiveRadiusResidualEndgamePacket_scalarSelector68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusScalarFaces68

end LaterDeepFiveRadiusScalarFaces68

end Max11DegreeRoutes
