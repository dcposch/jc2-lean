import LowScale68SecondaryResidualSelector

/-! # Defects below the selected `(6,8)` residual middle face

The selected middle face cancels two natural polynomial combinations.  This
module packages those combinations and the exact syzygies which expose the
next Newton comparison.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryResidualDescent68

variable {k : Type*} [Field k] [CharZero k]

/-- The quadratic discriminant combination cancelled on the selected middle
face. -/
def secondaryResidualDiscriminantPolynomial68
    (A B c : k[X]) : k[X] :=
  A * B ^ 2 + (3 : k) • c ^ 2

/-- The quartic invariant, normalized to remove its explicit `B^3` term. -/
def secondaryResidualIncidenceDefectPolynomial68
    (B c d e : k[X]) : k[X] :=
  B * e + c * d - (1 / 9 : k) • B ^ 3

/-- The next combination exposed by the cubic invariant after the incidence
defect has been removed. -/
def secondaryResidualCubicDefectPolynomial68
    (A B c d : k[X]) : k[X] :=
  (-2 : k) • (d * secondaryResidualDiscriminantPolynomial68 A B c) +
    (3 : k) • (B * d ^ 2) - (4 / 3 : k) • (B ^ 3 * c)

theorem secondaryResidualInvariantFourPolynomial68_eq_incidenceDefect
    (B c d e : k[X]) :
    secondaryResidualInvariantFourPolynomial68 B c d e =
      (8 / 3 : k) • secondaryResidualIncidenceDefectPolynomial68 B c d e := by
  simp only [secondaryResidualInvariantFourPolynomial68,
    secondaryResidualIncidenceDefectPolynomial68]
  module

set_option maxHeartbeats 1000000 in
/-- Multiplying the cubic invariant by `B` exposes the cubic defect, modulo
the already-normalized incidence defect. -/
theorem secondaryResidualInvariantThreePolynomial68_mul_eq_cubicDefect
    (A B c d e : k[X]) :
    B * secondaryResidualInvariantThreePolynomial68 A B c d e =
      (4 / 9 : k) • secondaryResidualCubicDefectPolynomial68 A B c d +
        (8 / 3 : k) •
          (c * secondaryResidualIncidenceDefectPolynomial68 B c d e) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [secondaryResidualInvariantThreePolynomial68,
    secondaryResidualCubicDefectPolynomial68,
    secondaryResidualDiscriminantPolynomial68,
    secondaryResidualIncidenceDefectPolynomial68,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_one]
  have hneg8 : RatFunc.C (-8 : k) = (-8 : RatFunc k) := by
    rw [show (-8 : k) = -(8 : k) by norm_num, map_neg, map_ofNat]
  rw [hneg8]
  ring

set_option maxHeartbeats 2000000 in
/-- Cancellation of the selected scalar discriminant strictly lowers the
corresponding polynomial discriminant. -/
theorem secondaryResidualDiscriminantPolynomial68_degree_lt
    (A B c : k[X]) (n g : ℕ) (hg : 0 < g) (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      3 * c.coeff (4 * n - g) ^ 2 = 0) :
    (secondaryResidualDiscriminantPolynomial68 A B c).natDegree <
      8 * n - 2 * g := by
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hdegree :
      (secondaryResidualDiscriminantPolynomial68 A B c).natDegree ≤
        8 * n - 2 * g := by
    simp only [secondaryResidualDiscriminantPolynomial68]
    compute_degree
    omega
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hAB2 := coeff_mul_at_bounds68 A (B ^ 2)
    (2 * n) (6 * n - 2 * g) hA hB2deg
  have hiAB : 2 * n + (6 * n - 2 * g) = 8 * n - 2 * g := by omega
  rw [hiAB, hB2] at hAB2
  have hc2 := coeff_pow_at_bound68 c (4 * n - g) 2 hc
  have hic : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
  rw [hic] at hc2
  have hcoeff : (secondaryResidualDiscriminantPolynomial68 A B c).coeff
      (8 * n - 2 * g) = 0 := by
    simp only [secondaryResidualDiscriminantPolynomial68, coeff_add,
      coeff_smul, hAB2, hc2, smul_eq_mul]
    exact hdisc
  exact (natDegree_le_pred hdegree hcoeff).trans_lt (by omega)

set_option maxHeartbeats 2000000 in
/-- The middle-face incidence equation likewise cancels the old top
coefficient of `B*e+c*d`. -/
theorem secondaryResidualIncidencePolynomial68_degree_lt
    (B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g) (hsmall : 3 * g < n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hincidence : B.coeff (3 * n - g) * e.coeff (6 * n - h) +
      c.coeff (4 * n - g) * d.coeff (5 * n - h) = 0) :
    (B * e + c * d).natDegree < 9 * n - g - h := by
  have hdegree : (B * e + c * d).natDegree ≤ 9 * n - g - h := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e
    (3 * n - g) (6 * n - h) hB he
  have hiBe : (3 * n - g) + (6 * n - h) = 9 * n - g - h := by omega
  rw [hiBe] at hBe
  have hcd := coeff_mul_at_bounds68 c d
    (4 * n - g) (5 * n - h) hc hd
  have hicd : (4 * n - g) + (5 * n - h) = 9 * n - g - h := by omega
  rw [hicd] at hcd
  have hcoeff : (B * e + c * d).coeff (9 * n - g - h) = 0 := by
    simp only [coeff_add, hBe, hcd]
    exact hincidence
  exact (natDegree_le_pred hdegree hcoeff).trans_lt (by omega)

set_option maxHeartbeats 2000000 in
/-- At the next cubic face, the quartic-invariant loads are still strictly
lower even though the two residual directions occur at the middle gap `h`. -/
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_cubicFace
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantFourPolynomial68
      l beta gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - 3 * g := by
  simp only [secondaryLoadInvariantFourPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
/-- The cubic-invariant loads obey the corresponding next-face cutoff. -/
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_cubicFace
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantThreePolynomial68
      l beta gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - 3 * g := by
  simp only [secondaryLoadInvariantThreePolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 3000000 in
/-- The exact quartic invariant lowers the normalized incidence defect below
the explicit `B^3` face. -/
theorem secondaryResidualIncidenceDefectPolynomial68_degree_lt_cubicFace
    (l beta gamma delta epsilon zeta i4 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (secondaryResidualIncidenceDefectPolynomial68 B c d e).natDegree <
      9 * n - 3 * g := by
  let D := (1 / 3 : k) • (A * B) + d
  let q := secondaryResidualIncidenceDefectPolynomial68 B c d e
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload := secondaryLoadInvariantFourPolynomial68_degree_lt_cubicFace
    l beta gamma delta epsilon zeta A B c D e n g h hg hgh hsmall
    hA hB hc hD he
  have hsplit := hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    cubicFirstIntegralFourPolynomial68_residualCoordinates,
    secondaryResidualInvariantFourPolynomial68_eq_incidenceDefect] at hsplit
  change (8 / 3 : k) • q +
    secondaryLoadInvariantFourPolynomial68
      l beta gamma delta epsilon zeta A B c D e = C i4 at hsplit
  have hcore : (8 / 3 : k) • q =
      C i4 - secondaryLoadInvariantFourPolynomial68
        l beta gamma delta epsilon zeta A B c D e :=
    eq_sub_iff_add_eq.mpr hsplit
  have hq : q = (3 / 8 : k) •
      (C i4 - secondaryLoadInvariantFourPolynomial68
        l beta gamma delta epsilon zeta A B c D e) := by
    calc
      q = (3 / 8 : k) • ((8 / 3 : k) • q) := by
        rw [smul_smul]
        norm_num
      _ = (3 / 8 : k) •
          (C i4 - secondaryLoadInvariantFourPolynomial68
            l beta gamma delta epsilon zeta A B c D e) := by rw [hcore]
  change q.natDegree < 9 * n - 3 * g
  rw [hq]
  compute_degree
  omega

set_option maxHeartbeats 4000000 in
/-- The cubic invariant and the quartic syzygy lower the next cubic defect
below the `B^3*c` face. -/
theorem secondaryResidualCubicDefectPolynomial68_degree_lt
    (l beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hsmall : 3 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    (secondaryResidualCubicDefectPolynomial68 A B c d).natDegree <
      13 * n - 4 * g := by
  let D := (1 / 3 : k) • (A * B) + d
  let q := secondaryResidualIncidenceDefectPolynomial68 B c d e
  let r := secondaryResidualCubicDefectPolynomial68 A B c d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hq := secondaryResidualIncidenceDefectPolynomial68_degree_lt_cubicFace
    l beta gamma delta epsilon zeta i4 A B c d e n g h hg hgh hsmall
    hA hB hc hd he hi4
  change q.natDegree < 9 * n - 3 * g at hq
  have hload := secondaryLoadInvariantThreePolynomial68_degree_lt_cubicFace
    l beta gamma delta epsilon zeta A B c D e n g h hg hgh hsmall
    hA hB hc hD he
  have hsplit := hi3
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    cubicFirstIntegralThreePolynomial68_residualCoordinates] at hsplit
  change secondaryResidualInvariantThreePolynomial68 A B c d e +
    secondaryLoadInvariantThreePolynomial68
      l beta gamma delta epsilon zeta A B c D e = C i3 at hsplit
  have hid := secondaryResidualInvariantThreePolynomial68_mul_eq_cubicDefect
    A B c d e
  change B * secondaryResidualInvariantThreePolynomial68 A B c d e =
    (4 / 9 : k) • r + (8 / 3 : k) • (c * q) at hid
  have hthree : secondaryResidualInvariantThreePolynomial68 A B c d e =
      C i3 - secondaryLoadInvariantThreePolynomial68
        l beta gamma delta epsilon zeta A B c D e :=
    eq_sub_iff_add_eq.mpr hsplit
  have hcore : (4 / 9 : k) • r =
      B * (C i3 - secondaryLoadInvariantThreePolynomial68
        l beta gamma delta epsilon zeta A B c D e) -
        (8 / 3 : k) • (c * q) := by
    apply eq_sub_iff_add_eq.mpr
    rw [← hthree]
    exact hid.symm
  have hr : r = (9 / 4 : k) •
      (B * (C i3 - secondaryLoadInvariantThreePolynomial68
        l beta gamma delta epsilon zeta A B c D e) -
        (8 / 3 : k) • (c * q)) := by
    calc
      r = (9 / 4 : k) • ((4 / 9 : k) • r) := by
        rw [smul_smul]
        norm_num
      _ = (9 / 4 : k) •
          (B * (C i3 - secondaryLoadInvariantThreePolynomial68
            l beta gamma delta epsilon zeta A B c D e) -
            (8 / 3 : k) • (c * q)) := by rw [hcore]
  change r.natDegree < 13 * n - 4 * g
  rw [hr]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
/-- The first residual one-form, rewritten through the normalized incidence
defect.  This identity separates the next comparison `2h` versus `3g`: all
terms involving the incidence defect are already below the latter face. -/
theorem secondaryResidualRowTwoPolynomial68_incidenceDefect
    (A B c d e : k[X]) :
    secondaryResidualRowTwoPolynomial68 A B c d e =
      (-4 / 27 : k) •
        (-(6 : k) •
            (A * derivative
              (secondaryResidualIncidenceDefectPolynomial68 B c d e)) +
          (3 : k) •
            (derivative A *
              secondaryResidualIncidenceDefectPolynomial68 B c d e) -
          (2 : k) • (A * B ^ 2 * derivative B) -
          (2 / 3 : k) • (derivative A * B ^ 3) +
          (6 : k) • derivative (B ^ 2 * d) +
          (6 : k) • derivative (B * c ^ 2) -
          (18 : k) • derivative (d * e)) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [secondaryResidualRowTwoPolynomial68,
    secondaryResidualIncidenceDefectPolynomial68,
    derivative_mul, derivative_pow, derivative_C,
    Polynomial.C_eq_natCast, Polynomial.smul_eq_C_mul, map_add,
    map_sub, map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 6000000 in
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

/-- If two nonzero polynomial terms dominate a lower remainder in a
vanishing sum, then the two displayed terms have the same degree. -/
private theorem natDegree_eq_of_two_terms_add_lower_eq_zero68
    (p q t : k[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (ht : t.natDegree < max p.natDegree q.natDegree)
    (hsum : p + q + t = 0) : p.natDegree = q.natDegree := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hpq | hqp
  · have hp0 := coeff_eq_zero_of_natDegree_lt hpq
    have ht0 : t.coeff q.natDegree = 0 := coeff_eq_zero_of_natDegree_lt (by
      rw [max_eq_right hpq.le] at ht
      exact ht)
    have hcoeff := congrArg (fun u : k[X] => u.coeff q.natDegree) hsum
    simp only [coeff_add, coeff_zero, hp0, ht0, zero_add, add_zero] at hcoeff
    have hq0 : q.coeff q.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hq
    exact hq0 hcoeff
  · have hq0 := coeff_eq_zero_of_natDegree_lt hqp
    have ht0 : t.coeff p.natDegree = 0 := coeff_eq_zero_of_natDegree_lt (by
      rw [max_eq_left hqp.le] at ht
      exact ht)
    have hcoeff := congrArg (fun u : k[X] => u.coeff p.natDegree) hsum
    simp only [coeff_add, coeff_zero, hq0, ht0, add_zero] at hcoeff
    have hp0 : p.coeff p.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hp
    exact hp0 hcoeff

/-- A nonzero polynomial cannot be cancelled by a strictly lower-degree
remainder. -/
private theorem singleTerm_add_lower_ne_zero68
    (p t : k[X]) (hp : p ≠ 0) (ht : t.natDegree < p.natDegree) :
    p + t ≠ 0 := by
  intro hsum
  have ht0 := coeff_eq_zero_of_natDegree_lt ht
  have hcoeff := congrArg (fun u : k[X] => u.coeff p.natDegree) hsum
  simp only [coeff_add, coeff_zero, ht0, add_zero] at hcoeff
  have hp0 : p.coeff p.natDegree ≠ 0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp
  exact hp0 hcoeff

set_option maxHeartbeats 3000000 in
/-- On the side `2h < 3g`, cancellation in the cubic defect forces the
discriminant defect to meet `B*d^2`.  In particular, its next gap is exactly
`g+h`. -/
theorem secondaryResidualCubicDefect_leftChamber68
    (A B c d : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n)
    (hleft : 2 * h < 3 * g)
    (hB0 : B ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (hBdeg : B.natDegree = 3 * n - g)
    (hcdeg : c.natDegree = 4 * n - g)
    (hddeg : d.natDegree = 5 * n - h)
    (hr : (secondaryResidualCubicDefectPolynomial68 A B c d).natDegree <
      13 * n - 4 * g) :
    let discr := secondaryResidualDiscriminantPolynomial68 A B c
    discr ≠ 0 ∧ discr.natDegree = 8 * n - g - h := by
  let discr := secondaryResidualDiscriminantPolynomial68 A B c
  let r := secondaryResidualCubicDefectPolynomial68 A B c d
  let p : k[X] := C (-2 : k) * (d * discr)
  let q : k[X] := C (3 : k) * (B * d ^ 2)
  let u : k[X] := -(C (4 / 3 : k) * (B ^ 3 * c))
  let t : k[X] := u - r
  change discr ≠ 0 ∧ discr.natDegree = 8 * n - g - h
  change r.natDegree < 13 * n - 4 * g at hr
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero (C_ne_zero.mpr (by norm_num))
      (mul_ne_zero hB0 (pow_ne_zero 2 hd0))
  have hqdeg : q.natDegree = 13 * n - g - 2 * h := by
    dsimp [q]
    rw [natDegree_C_mul (by norm_num),
      natDegree_mul hB0 (pow_ne_zero 2 hd0), natDegree_pow,
      hBdeg, hddeg]
    omega
  have hudeg : u.natDegree = 13 * n - 4 * g := by
    dsimp [u]
    rw [natDegree_neg, natDegree_C_mul (by norm_num),
      natDegree_mul (pow_ne_zero 3 hB0) hc0, natDegree_pow,
      hBdeg, hcdeg]
    omega
  have ht : t.natDegree < q.natDegree := by
    dsimp [t]
    have hsub := natDegree_sub_le u r
    rw [hudeg] at hsub
    rw [hqdeg]
    omega
  have hsum : p + q + t = 0 := by
    dsimp [p, q, u, t, r, discr,
      secondaryResidualCubicDefectPolynomial68]
    simp only [Polynomial.smul_eq_C_mul]
    module
  have hdiscr0 : discr ≠ 0 := by
    intro hzero
    have hpzero : p = 0 := by simp [p, hzero]
    have hqt : q + t = 0 := by simpa only [hpzero, zero_add] using hsum
    exact singleTerm_add_lower_ne_zero68 q t hq0 ht hqt
  have hp0 : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (C_ne_zero.mpr (by norm_num))
      (mul_ne_zero hd0 hdiscr0)
  have hpdeg : p.natDegree = d.natDegree + discr.natDegree := by
    dsimp [p]
    rw [natDegree_C_mul (by norm_num), natDegree_mul hd0 hdiscr0]
  have htmax : t.natDegree < max p.natDegree q.natDegree :=
    ht.trans_le (Nat.le_max_right _ _)
  have hdegrees := natDegree_eq_of_two_terms_add_lower_eq_zero68
    p q t hp0 hq0 htmax hsum
  constructor
  · exact hdiscr0
  · rw [hpdeg, hqdeg, hddeg] at hdegrees
    omega

set_option maxHeartbeats 3000000 in
/-- On the side `3g < 2h`, cancellation in the cubic defect forces the
discriminant defect to meet `B^3*c`.  Its next gap is exactly `4g-h`. -/
theorem secondaryResidualCubicDefect_rightChamber68
    (A B c d : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n)
    (hright : 3 * g < 2 * h)
    (hB0 : B ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (hBdeg : B.natDegree = 3 * n - g)
    (hcdeg : c.natDegree = 4 * n - g)
    (hddeg : d.natDegree = 5 * n - h)
    (hr : (secondaryResidualCubicDefectPolynomial68 A B c d).natDegree <
      13 * n - 4 * g) :
    let discr := secondaryResidualDiscriminantPolynomial68 A B c
    discr ≠ 0 ∧ discr.natDegree = 8 * n - 4 * g + h := by
  let discr := secondaryResidualDiscriminantPolynomial68 A B c
  let r := secondaryResidualCubicDefectPolynomial68 A B c d
  let p : k[X] := C (-2 : k) * (d * discr)
  let q : k[X] := -(C (4 / 3 : k) * (B ^ 3 * c))
  let u : k[X] := C (3 : k) * (B * d ^ 2)
  let t : k[X] := u - r
  change discr ≠ 0 ∧ discr.natDegree = 8 * n - 4 * g + h
  change r.natDegree < 13 * n - 4 * g at hr
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (by norm_num))
      (mul_ne_zero (pow_ne_zero 3 hB0) hc0))
  have hqdeg : q.natDegree = 13 * n - 4 * g := by
    dsimp [q]
    rw [natDegree_neg, natDegree_C_mul (by norm_num),
      natDegree_mul (pow_ne_zero 3 hB0) hc0, natDegree_pow,
      hBdeg, hcdeg]
    omega
  have hudeg : u.natDegree = 13 * n - g - 2 * h := by
    dsimp [u]
    rw [natDegree_C_mul (by norm_num),
      natDegree_mul hB0 (pow_ne_zero 2 hd0), natDegree_pow,
      hBdeg, hddeg]
    omega
  have ht : t.natDegree < q.natDegree := by
    dsimp [t]
    have hsub := natDegree_sub_le u r
    rw [hudeg] at hsub
    rw [hqdeg]
    omega
  have hsum : p + q + t = 0 := by
    dsimp [p, q, u, t, r, discr,
      secondaryResidualCubicDefectPolynomial68]
    simp only [Polynomial.smul_eq_C_mul]
    module
  have hdiscr0 : discr ≠ 0 := by
    intro hzero
    have hpzero : p = 0 := by simp [p, hzero]
    have hqt : q + t = 0 := by simpa only [hpzero, zero_add] using hsum
    exact singleTerm_add_lower_ne_zero68 q t hq0 ht hqt
  have hp0 : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (C_ne_zero.mpr (by norm_num))
      (mul_ne_zero hd0 hdiscr0)
  have hpdeg : p.natDegree = d.natDegree + discr.natDegree := by
    dsimp [p]
    rw [natDegree_C_mul (by norm_num), natDegree_mul hd0 hdiscr0]
  have htmax : t.natDegree < max p.natDegree q.natDegree :=
    ht.trans_le (Nat.le_max_right _ _)
  have hdegrees := natDegree_eq_of_two_terms_add_lower_eq_zero68
    p q t hp0 hq0 htmax hsum
  constructor
  · exact hdiscr0
  · rw [hpdeg, hqdeg, hddeg] at hdegrees
    omega

set_option maxHeartbeats 4000000 in
/-- On the balanced face `2h = 3g`, the discriminant defect cannot lie above
the common cubic face.  Its boundary coefficient participates in the exact
three-term face equation, and is allowed to vanish if the other two terms
already cancel. -/
theorem secondaryResidualCubicDefect_balancedChamber68
    (A B c d : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hh : h < 2 * g)
    (hsmall : 3 * g < n) (hbalanced : 2 * h = 3 * g)
    (hB0 : B ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (hBdeg : B.natDegree = 3 * n - g)
    (hcdeg : c.natDegree = 4 * n - g)
    (hddeg : d.natDegree = 5 * n - h)
    (hr : (secondaryResidualCubicDefectPolynomial68 A B c d).natDegree <
      13 * n - 4 * g) :
    let discr := secondaryResidualDiscriminantPolynomial68 A B c
    discr.natDegree ≤ 8 * n - 4 * g + h ∧
      (-2 : k) *
          (d.coeff (5 * n - h) * discr.coeff (8 * n - 4 * g + h)) +
        3 * (B.coeff (3 * n - g) * d.coeff (5 * n - h) ^ 2) -
        (4 / 3 : k) *
          (B.coeff (3 * n - g) ^ 3 * c.coeff (4 * n - g)) = 0 := by
  let discr := secondaryResidualDiscriminantPolynomial68 A B c
  let r := secondaryResidualCubicDefectPolynomial68 A B c d
  let p : k[X] := C (-2 : k) * (d * discr)
  let q : k[X] := C (3 : k) * (B * d ^ 2)
  let u : k[X] := C (4 / 3 : k) * (B ^ 3 * c)
  let t : k[X] := q - u - r
  change discr.natDegree ≤ 8 * n - 4 * g + h ∧ _
  change r.natDegree < 13 * n - 4 * g at hr
  have hqdeg : q.natDegree = 13 * n - 4 * g := by
    dsimp [q]
    rw [natDegree_C_mul (by norm_num),
      natDegree_mul hB0 (pow_ne_zero 2 hd0), natDegree_pow,
      hBdeg, hddeg]
    omega
  have hudeg : u.natDegree = 13 * n - 4 * g := by
    dsimp [u]
    rw [natDegree_C_mul (by norm_num),
      natDegree_mul (pow_ne_zero 3 hB0) hc0, natDegree_pow,
      hBdeg, hcdeg]
    omega
  have htdeg : t.natDegree ≤ 13 * n - 4 * g := by
    dsimp [t]
    have hqu := natDegree_sub_le q u
    have htur := natDegree_sub_le (q - u) r
    rw [hqdeg, hudeg] at hqu
    omega
  have hsum : p + t = 0 := by
    dsimp [p, q, u, t, r, discr,
      secondaryResidualCubicDefectPolynomial68]
    simp only [Polynomial.smul_eq_C_mul]
    module
  have hdiscle : discr.natDegree ≤ 8 * n - 4 * g + h := by
    by_cases hdiscr0 : discr = 0
    · simp only [hdiscr0, natDegree_zero]
      omega
    · by_contra hnotle
      have hp0 : p ≠ 0 := by
        dsimp [p]
        exact mul_ne_zero (C_ne_zero.mpr (by norm_num))
          (mul_ne_zero hd0 hdiscr0)
      have hpdeg : p.natDegree = d.natDegree + discr.natDegree := by
        dsimp [p]
        rw [natDegree_C_mul (by norm_num), natDegree_mul hd0 hdiscr0]
      have hptop : 13 * n - 4 * g < p.natDegree := by
        rw [hpdeg, hddeg]
        omega
      have htlower : t.natDegree < p.natDegree := htdeg.trans_lt hptop
      exact singleTerm_add_lower_ne_zero68 p t hp0 htlower hsum
  constructor
  · exact hdiscle
  · have hdDiscr := coeff_mul_at_bounds68 d discr
      (5 * n - h) (8 * n - 4 * g + h) hddeg.le hdiscle
    have hiD : (5 * n - h) + (8 * n - 4 * g + h) =
        13 * n - 4 * g := by omega
    rw [hiD] at hdDiscr
    have hd2deg : (d ^ 2).natDegree ≤ 2 * (5 * n - h) := by
      compute_degree
      omega
    have hd2 := coeff_pow_at_bound68 d (5 * n - h) 2 hddeg.le
    have hBd2 := coeff_mul_at_bounds68 B (d ^ 2)
      (3 * n - g) (2 * (5 * n - h)) hBdeg.le hd2deg
    have hiBd2 : (3 * n - g) + 2 * (5 * n - h) =
        13 * n - 4 * g := by omega
    rw [hiBd2, hd2] at hBd2
    have hB3deg : (B ^ 3).natDegree ≤ 3 * (3 * n - g) := by
      compute_degree
      omega
    have hB3 := coeff_pow_at_bound68 B (3 * n - g) 3 hBdeg.le
    have hB3c := coeff_mul_at_bounds68 (B ^ 3) c
      (3 * (3 * n - g)) (4 * n - g) hB3deg hcdeg.le
    have hiB3c : 3 * (3 * n - g) + (4 * n - g) =
        13 * n - 4 * g := by omega
    rw [hiB3c, hB3] at hB3c
    have hr0 : r.coeff (13 * n - 4 * g) = 0 :=
      coeff_eq_zero_of_natDegree_lt hr
    change (((-2 : k) • (d * discr) + (3 : k) • (B * d ^ 2) -
      (4 / 3 : k) • (B ^ 3 * c)).coeff (13 * n - 4 * g)) = 0 at hr0
    simp only [coeff_add, coeff_sub, coeff_smul, hdDiscr, hBd2, hB3c,
      smul_eq_mul] at hr0
    exact hr0

end SecondaryResidualDescent68

#print axioms secondaryResidualInvariantFourPolynomial68_eq_incidenceDefect
#print axioms secondaryResidualInvariantThreePolynomial68_mul_eq_cubicDefect
#print axioms secondaryResidualDiscriminantPolynomial68_degree_lt
#print axioms secondaryResidualIncidencePolynomial68_degree_lt
#print axioms secondaryLoadInvariantFourPolynomial68_degree_lt_cubicFace
#print axioms secondaryLoadInvariantThreePolynomial68_degree_lt_cubicFace
#print axioms secondaryResidualIncidenceDefectPolynomial68_degree_lt_cubicFace
#print axioms secondaryResidualCubicDefectPolynomial68_degree_lt
#print axioms secondaryResidualRowTwoPolynomial68_incidenceDefect
#print axioms cubicLoadRowTwoPolynomial68_degree_lt_cubicFace
#print axioms secondaryResidualCubicDefect_leftChamber68
#print axioms secondaryResidualCubicDefect_rightChamber68
#print axioms secondaryResidualCubicDefect_balancedChamber68

end Max11DegreeRoutes
