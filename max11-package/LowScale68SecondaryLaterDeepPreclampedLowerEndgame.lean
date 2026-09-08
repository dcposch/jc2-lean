import LowScale68SecondaryLaterDeepPreclampedEndgame

/-! # Lower preclamped later-deep faces

This file continues the exact `6n < 2g ≤ 7n` faces.  In the open chamber,
the I4/I3/row-one packet forces the unique attained secondary coordinate to
be `c`; equivalently the top coefficients of `B,D,e` vanish and `c_top≠0`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepPreclampedLower68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact second lower row after `l=beta=delta=0` and `B=0`, in cubic
coordinates.  This identity is useful beyond a single Newton chamber. -/
theorem lowerRowOnePolynomial68_B_zero_exact
    (alpha gamma epsilon zeta eta : k) (A c D e : k[X]) :
    lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A 0
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A 0
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A 0
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
    (8 / 9 : k) • (A * c * derivative e) +
      (8 / 9 : k) • (A * e * derivative c) +
      (2 / 3 * epsilon : k) • (A * derivative c) +
      (4 / 3 * gamma : k) • (A * derivative e) -
      (8 / 9 : k) • (c ^ 2 * derivative c) -
      (4 / 3 * gamma : k) • (c * derivative c) -
      (4 / 9 : k) • (D ^ 2 * derivative A) +
      (8 / 3 : k) • (e * derivative e) +
      zeta • derivative D + (2 * epsilon : k) • derivative e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [lowerRowOnePolynomial68, integratedTPolynomial68,
    integratedUPolynomial68, integratedVPolynomial68, derivative_add,
    derivative_sub, derivative_smul, derivative_mul, derivative_pow,
    derivative_C, zero_pow, zero_smul, smul_zero, zero_mul, mul_zero,
    add_zero, zero_add, sub_zero, Polynomial.C_eq_natCast,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, map_zero, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-- The ordinary I3 secondary face remains load-free throughout
`5n < 2g ≤ 6n` after `l=beta=delta=0`. -/
theorem cubicFirstIntegralThreePolynomial68_fiveToSix_face
    (gamma epsilon zeta i3 : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hI3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c D e = C i3) :
    firstSecondaryThree68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 := by
  let j := 10 * n - 2 * g
  have lower (p : k[X]) (hp : p.natDegree < j) : p.coeff j = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by compute_degree; omega
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
  have hA2B2 : (A ^ 2 * B ^ 2).coeff j =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_mul_at_bounds68 (A ^ 2) (B ^ 2) (4 * n)
      (6 * n - 2 * g) hA2deg hB2deg
    have hi : 4 * n + (6 * n - 2 * g) = j := by dsimp only [j]; omega
    simpa only [hi, hA2coeff, hB2coeff] using h
  have hABD : (A * B * D).coeff j =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        D.coeff (5 * n - g) := by
    have h := coeff_mul_mul_at_bounds68 A B D (2 * n)
      (3 * n - g) (5 * n - g) hA hB hD
    have hi : 2 * n + (3 * n - g) + (5 * n - g) = j := by
      dsimp only [j]
      omega
    simpa only [hi] using h
  have hD2 : (D ^ 2).coeff j = D.coeff (5 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 D (5 * n - g) 2 hD
    have hi : 2 * (5 * n - g) = j := by dsimp only [j]; omega
    simpa only [hi] using h
  have hce : (c * e).coeff j =
      c.coeff (4 * n - g) * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - g) hc he
    have hi : (4 * n - g) + (6 * n - g) = j := by dsimp only [j]; omega
    simpa only [hi] using h
  have hB2c : (B ^ 2 * c).natDegree < j := by
    dsimp only [j]
    compute_degree
    omega
  have hBlt : B.natDegree < j := by dsimp only [j]; omega
  have hclt : c.natDegree < j := by dsimp only [j]; omega
  have helt : e.natDegree < j := by dsimp only [j]; omega
  have hB2lt : (B ^ 2).natDegree < j := by
    dsimp only [j]
    compute_degree
    omega
  have hcoeff := congrArg (fun p : k[X] ↦ p.coeff j) hI3
  simp only [cubicFirstIntegralThreePolynomial68, coeff_add, coeff_sub,
    coeff_smul, hA2B2, hABD, lower _ hB2c, hD2, hce,
    lower _ hBlt, lower _ hclt, lower _ helt, lower _ hB2lt,
    smul_eq_mul, zero_add, add_zero, zero_sub, sub_zero] at hcoeff
  have hj0 : j ≠ 0 := by dsimp only [j]; omega
  simp only [coeff_C, if_neg hj0] at hcoeff
  have hscaled : (4 / 9 : k) * firstSecondaryThree68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 := by
    simp only [firstSecondaryThree68]
    linear_combination hcoeff
  exact (mul_eq_zero.mp hscaled).resolve_left (by norm_num)

set_option maxHeartbeats 10000000 in
/-- Canonical ordinary invariant packet in `5n < 2g ≤ 6n`.  Both
first-secondary invariant scalars survive unchanged after the forced
vanishings `l=beta=delta=0`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_invariantFaces68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      5 * n < 2 * g ∧ 2 * g ≤ 6 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    firstSecondaryFour68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
      (ee.coeff (6 * n - g)) = 0 ∧
    firstSecondaryThree68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
      (ee.coeff (6 * n - g)) = 0 := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n at hwindow
  change firstSecondaryFour68 _ _ _ _ _ = 0 ∧
    firstSecondaryThree68 _ _ _ _ _ = 0
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hgt3 : 3 * n < 2 * g := by omega
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  obtain ⟨i4, hI4raw⟩ := data.invariant
  have hI4 := hI4raw
  rw [hl, hbeta] at hI4
  have hdelta :=
    cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
      gamma delta epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
      hwindow.1 data.hA data.hB data.hc data.hD data.he data.ha hI4
  rw [hdelta] at hI4
  have hfour :=
    cubicFirstIntegralFourPolynomial68_postDelta_forces_face
      gamma epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
      hwindow data.hA data.hB data.hc data.hD data.he hI4
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hl, hbeta, hdelta] at hi3e
  have hthree := cubicFirstIntegralThreePolynomial68_fiveToSix_face
    gamma epsilon zeta i3 Ae Be ce De ee n g data.hn hwindow
    data.hA data.hB data.hc data.hD data.he hi3e
  exact ⟨hfour, hthree⟩

/-- The I3 face in `6n < 2g ≤ 7n`, after `B=0`. -/
theorem cubicFirstIntegralThreePolynomial68_sixToSeven_face
    (gamma epsilon zeta i3 : k) (A c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 6 * n < 2 * g ∧ 2 * g ≤ 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hI3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A 0 c D e = C i3) :
    D.coeff (5 * n - g) ^ 2 +
      2 * c.coeff (4 * n - g) * e.coeff (6 * n - g) = 0 := by
  let j := 10 * n - 2 * g
  have hD2 : (D ^ 2).coeff j = D.coeff (5 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 D (5 * n - g) 2 hD
    have hj : 2 * (5 * n - g) = j := by dsimp only [j]; omega
    simpa only [hj] using h
  have hce : (c * e).coeff j =
      c.coeff (4 * n - g) * e.coeff (6 * n - g) := by
    have h := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - g) hc he
    have hj : (4 * n - g) + (6 * n - g) = j := by dsimp only [j]; omega
    simpa only [hj] using h
  have hcLt : c.natDegree < j := by dsimp only [j]; omega
  have heLt : e.natDegree < j := by dsimp only [j]; omega
  have hcoeff := congrArg (fun p : k[X] ↦ p.coeff j) hI3
  have hzero2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by norm_num)
  simp only [cubicFirstIntegralThreePolynomial68, hzero2, zero_smul,
    smul_zero, zero_mul, mul_zero, add_zero, zero_add, sub_zero,
    coeff_add, coeff_sub, coeff_smul, hD2, hce,
    coeff_eq_zero_of_natDegree_lt hcLt,
    coeff_eq_zero_of_natDegree_lt heLt, smul_eq_mul] at hcoeff
  have hj0 : j ≠ 0 := by dsimp only [j]; omega
  simp only [coeff_C, if_neg hj0] at hcoeff
  linear_combination (3 / 4 : k) * hcoeff

/-- Once the I4/I3 faces have killed `D_top` and `c_top*e_top`, row one
kills `e_top`. -/
theorem lowerRowOnePolynomial68_sixToSeven_forces_e_top_zero
    (alpha gamma epsilon zeta eta : k) (A c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 6 * n < 2 * g ∧ 2 * g < 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hcTop : c.coeff (4 * n - g) = 0)
    (hDTop : D.coeff (5 * n - g) = 0)
    (hrow : lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A 0
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A 0
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A 0
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = 0) :
    e.coeff (6 * n - g) = 0 := by
  let j := 12 * n - 2 * g - 1
  have hc' : c.natDegree < 4 * n - g :=
    natDegree_lt_of_le_of_coeff_eq_zero68 c (4 * n - g) (by omega) hc hcTop
  have hD' : D.natDegree < 5 * n - g :=
    natDegree_lt_of_le_of_coeff_eq_zero68 D (5 * n - g) (by omega) hD hDTop
  have lower (p : k[X]) (hp : p.natDegree < j) : p.coeff j = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hAce : (A * c * derivative e).natDegree < j := by
    compute_degree
    omega
  have hAec : (A * e * derivative c).natDegree < j := by
    compute_degree
    omega
  have hAc : (A * derivative c).natDegree < j := by
    compute_degree
    omega
  have hAe : (A * derivative e).natDegree < j := by
    compute_degree
    omega
  have hc2c : (c ^ 2 * derivative c).natDegree < j := by
    compute_degree
    omega
  have hcc : (c * derivative c).natDegree < j := by
    compute_degree
    omega
  have hD2A : (D ^ 2 * derivative A).natDegree < j := by
    compute_degree
    omega
  have hDder : (derivative D).natDegree < j := by
    compute_degree
    omega
  have heder : (derivative e).natDegree < j := by
    compute_degree
    omega
  have hee : (e * derivative e).coeff j =
      e.coeff (6 * n - g) ^ 2 * ((6 * n - g : ℕ) : k) := by
    have hp := coeff_mul_derivative_at_bounds68 e e (6 * n - g)
      (6 * n - g) (by omega) he he
    have hj : (6 * n - g) + (6 * n - g) - 1 = j := by
      dsimp only [j]
      omega
    simpa only [hj, pow_two, mul_assoc] using hp
  have hcoeff := congrArg (fun p : k[X] ↦ p.coeff j) hrow
  rw [lowerRowOnePolynomial68_B_zero_exact] at hcoeff
  simp only [coeff_add, coeff_sub, coeff_smul, lower _ hAce, lower _ hAec,
    lower _ hAc, lower _ hAe, lower _ hc2c, lower _ hcc, lower _ hD2A,
    lower _ hDder, lower _ heder, hee, smul_eq_mul, zero_add, add_zero,
    zero_sub, sub_zero] at hcoeff
  have hj0 : j ≠ 0 := by dsimp only [j]; omega
  simp only [coeff_zero] at hcoeff
  have hweightNat : 0 < 6 * n - g := by omega
  have hweight : (((6 * n - g : ℕ) : k)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hweightNat)
  have hsquare : e.coeff (6 * n - g) ^ 2 = 0 := by
    have hz : (8 / 3 : k) *
        (e.coeff (6 * n - g) ^ 2 * (((6 * n - g : ℕ) : k))) = 0 :=
      by simpa only [zero_mul, mul_zero, zero_add, add_zero, zero_sub,
        sub_zero] using hcoeff
    have hinner : e.coeff (6 * n - g) ^ 2 *
        (((6 * n - g : ℕ) : k)) = 0 :=
      (mul_eq_zero.mp hz).resolve_left (by norm_num)
    exact (mul_eq_zero.mp hinner).resolve_right hweight
  exact eq_zero_of_pow_eq_zero hsquare

set_option maxHeartbeats 10000000 in
/-- Canonical classification of the open `6n < 2g < 7n` chamber: `c` is
the unique secondary coordinate which attains the defect boundary. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_sixToSeven_c_only_top68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      6 * n < 2 * g ∧ 2 * g < 7 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    Be = 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      De.coeff (5 * n - g) = 0 ∧ ee.coeff (6 * n - g) = 0 := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 6 * n < 2 * g ∧ 2 * g < 7 * n at hwindow
  change Be = 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
    De.coeff (5 * n - g) = 0 ∧ ee.coeff (6 * n - g) = 0
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hn : 0 < n := data.hn
  have hgt3 : 3 * n < 2 * g := by omega
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  obtain ⟨i4, hI4raw⟩ := data.invariant
  have hI4 := hI4raw
  rw [hl, hbeta] at hI4
  have hdelta :=
    cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
      gamma delta epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
      (by omega) data.hA data.hB data.hc data.hD data.he data.ha hI4
  rw [hdelta] at hI4
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hl, hbeta, hdelta] at hi3e
  have hBe :=
    cubicFirstIntegralThreePolynomial68_forces_B_zero_of_sixRadius_lt_twoGap
      gamma epsilon zeta i3 Ae Be ce De ee n g data.hn hwindow.1
      data.hA data.hB data.hc data.hD data.he data.ha hi3e
  rw [hBe] at hI4 hi3e
  have hDc := cubicFirstIntegralFourPolynomial68_sixToSeven_forces_Dc_face
    gamma epsilon zeta i4 Ae ce De ee n g data.hn hwindow data.hA data.hc
    data.hD data.he hI4
  have hface3 := cubicFirstIntegralThreePolynomial68_sixToSeven_face
    gamma epsilon zeta i3 Ae ce De ee n g data.hn
    ⟨hwindow.1, le_of_lt hwindow.2⟩ data.hA data.hc
    data.hD data.he hi3e
  let ctop := ce.coeff (4 * n - g)
  let dtop := De.coeff (5 * n - g)
  let etop := ee.coeff (6 * n - g)
  change dtop * ctop = 0 at hDc
  change dtop ^ 2 + 2 * ctop * etop = 0 at hface3
  have hdtop : dtop = 0 := by
    by_contra hd
    have hc : ctop = 0 := (mul_eq_zero.mp hDc).resolve_left hd
    rw [hc, mul_zero, zero_mul, add_zero] at hface3
    exact hd (eq_zero_of_pow_eq_zero hface3)
  have hce : ctop * etop = 0 := by
    rw [hdtop, zero_pow (by norm_num), zero_add] at hface3
    have hfactor : (2 : k) * (ctop * etop) = 0 := by
      simpa only [mul_assoc] using hface3
    exact (mul_eq_zero.mp hfactor).resolve_left (by norm_num)
  have hrowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hl, hbeta, hdelta, hBe, hCrec, hErec] at hrowOne
  have hetop_of_hc (hc : ctop = 0) : etop = 0 := by
    exact lowerRowOnePolynomial68_sixToSeven_forces_e_top_zero
      alpha gamma epsilon zeta eta Ae ce De ee n g data.hn hwindow
      data.hA data.hc data.hD data.he (by simpa only [ctop] using hc)
      (by simpa only [dtop] using hdtop) hrowOne
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
    ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
    ee.natDegree ≤ 6 * n - g ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ctop ≠ 0 ∨ dtop ≠ 0 ∨ etop ≠ 0)
      at hsecondary
  have hctop : ctop ≠ 0 := by
    intro hc
    have he : etop = 0 := hetop_of_hc hc
    rcases hsecondary.2.2.2.2.2 with hBt | hct | hdt | het
    · exact hBt (by rw [hBe, coeff_zero])
    · exact hct hc
    · exact hdt hdtop
    · exact het he
  have hetop : etop = 0 := (mul_eq_zero.mp hce).resolve_left hctop
  exact ⟨hBe, by simpa only [ctop] using hctop,
    by simpa only [dtop] using hdtop, by simpa only [etop] using hetop⟩

/-- After `c` uniquely attains the secondary boundary, the exact I4 equation
drops the whole polynomial `D` from `5n-g` to `g-2n`. -/
theorem cubicFirstIntegralFourPolynomial68_c_top_forces_D_degree_drop
    (gamma epsilon zeta i4 : k) (A c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 6 * n < 2 * g ∧ 2 * g < 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (hcTop : c.coeff (4 * n - g) ≠ 0)
    (hD0 : D ≠ 0)
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A 0 c D e = C i4) :
    D.natDegree ≤ g - 2 * n := by
  let m := 4 * n - g
  let s : k[X] := (2 / 3 : k) • c + C gamma
  have hm : 0 < m := by dsimp only [m]; omega
  have hcdeg : c.natDegree = m := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · simpa only [m] using hc
    · simpa only [m] using hcTop
  have hsle : s.natDegree ≤ m := by
    simp only [s]
    compute_degree
    omega
  have hscoeff : s.coeff m = (2 / 3 : k) * c.coeff m := by
    simp only [s, coeff_add, coeff_smul, coeff_C, if_neg (Nat.ne_of_gt hm),
      add_zero, smul_eq_mul]
  have hscoeff0 : s.coeff m ≠ 0 := by
    rw [hscoeff]
    exact mul_ne_zero (by norm_num) (by simpa only [m] using hcTop)
  have hsdeg : s.natDegree = m := natDegree_eq_of_le_of_coeff_ne_zero hsle hscoeff0
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz, coeff_zero] at hscoeff0
    exact hscoeff0 rfl
  have hEq : (4 : k) • (D * s) = C i4 - zeta • A := by
    rw [← hI4]
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [s, cubicFirstIntegralFourPolynomial68,
      Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_neg, map_zero, RatFunc.algebraMap_C]
    simp only [map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hrhs : (C i4 - zeta • A).natDegree ≤ 2 * n := by
    compute_degree
    omega
  have hdegree : D.natDegree + m ≤ 2 * n := by
    calc
      D.natDegree + m = (D * s).natDegree := by
        rw [natDegree_mul hD0 hs0, hsdeg]
      _ = ((4 : k) • (D * s)).natDegree := by
        rw [natDegree_smul _ (by norm_num : (4 : k) ≠ 0)]
      _ = (C i4 - zeta • A).natDegree := congrArg natDegree hEq
      _ ≤ 2 * n := hrhs
  dsimp only [m] at hdegree
  omega

/-- Exact row-one scalar on the wall `2g=7n`, after `B=0`. -/
theorem lowerRowOnePolynomial68_sevenRadiusWall_relation
    (alpha gamma epsilon zeta eta : k) (A c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hrow : lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A 0
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A 0
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A 0
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = 0) :
    (8 / 9 : k) * A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (6 * n - g) * ((6 * n - g : ℕ) : k) +
      (8 / 9 : k) * A.coeff (2 * n) * e.coeff (6 * n - g) *
        c.coeff (4 * n - g) * ((4 * n - g : ℕ) : k) -
      (4 / 9 : k) * D.coeff (5 * n - g) ^ 2 *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) +
      (8 / 3 : k) * e.coeff (6 * n - g) ^ 2 *
        ((6 * n - g : ℕ) : k) = 0 := by
  let j := 12 * n - 2 * g - 1
  have hcpos : 0 < 4 * n - g := by omega
  have hepos : 0 < 6 * n - g := by omega
  have hApos : 0 < 2 * n := by omega
  have hAce : (A * c * derivative e).coeff j =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (6 * n - g) * ((6 * n - g : ℕ) : k) := by
    have hp := coeff_mul_mul_derivative_at_bounds68 A c e (2 * n)
      (4 * n - g) (6 * n - g) hepos hA hc he
    have hj : 2 * n + (4 * n - g) + (6 * n - g) - 1 = j := by
      dsimp only [j]
      omega
    simpa only [hj, mul_assoc] using hp
  have hAec : (A * e * derivative c).coeff j =
      A.coeff (2 * n) * e.coeff (6 * n - g) *
        c.coeff (4 * n - g) * ((4 * n - g : ℕ) : k) := by
    have hp := coeff_mul_mul_derivative_at_bounds68 A e c (2 * n)
      (6 * n - g) (4 * n - g) hcpos hA he hc
    have hj : 2 * n + (6 * n - g) + (4 * n - g) - 1 = j := by
      dsimp only [j]
      omega
    simpa only [hj, mul_assoc] using hp
  have hD2A : (D ^ 2 * derivative A).coeff j =
      D.coeff (5 * n - g) ^ 2 * A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have hp := coeff_mul_mul_derivative_at_bounds68 D D A (5 * n - g)
      (5 * n - g) (2 * n) hApos hD hD hA
    have hj : (5 * n - g) + (5 * n - g) + 2 * n - 1 = j := by
      dsimp only [j]
      omega
    simpa only [hj, pow_two, mul_assoc] using hp
  have hee : (e * derivative e).coeff j =
      e.coeff (6 * n - g) ^ 2 * ((6 * n - g : ℕ) : k) := by
    have hp := coeff_mul_derivative_at_bounds68 e e (6 * n - g)
      (6 * n - g) hepos he he
    have hj : (6 * n - g) + (6 * n - g) - 1 = j := by
      dsimp only [j]
      omega
    simpa only [hj, pow_two, mul_assoc] using hp
  have lower (p : k[X]) (hp : p.natDegree < j) : p.coeff j = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hAc : (A * derivative c).natDegree < j := by compute_degree; omega
  have hAe : (A * derivative e).natDegree < j := by compute_degree; omega
  have hc2c : (c ^ 2 * derivative c).natDegree < j := by compute_degree; omega
  have hcc : (c * derivative c).natDegree < j := by compute_degree; omega
  have hDder : (derivative D).natDegree < j := by compute_degree; omega
  have heder : (derivative e).natDegree < j := by compute_degree; omega
  have hcoeff := congrArg (fun p : k[X] ↦ p.coeff j) hrow
  rw [lowerRowOnePolynomial68_B_zero_exact] at hcoeff
  simp only [coeff_add, coeff_sub, coeff_smul, hAce, hAec, hD2A, hee,
    lower _ hAc, lower _ hAe, lower _ hc2c, lower _ hcc,
    lower _ hDder, lower _ heder, smul_eq_mul, zero_add, add_zero,
    zero_sub, sub_zero, coeff_zero] at hcoeff
  simpa only [mul_zero, zero_mul, zero_add, add_zero, sub_zero,
    mul_assoc] using hcoeff

/-- On the seven-radius wall the I3 face removes the `D_top^2` term from
row one, leaving a two-factor scalar alternative for `e_top`. -/
theorem sevenRadiusWall_i3_rowOne_forces_e_factor68
    (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 7 * n)
    (a c d e : k)
    (hi3 : d ^ 2 + 2 * c * e = 0)
    (hrow :
      (8 / 9 : k) * a * c * e * ((6 * n - g : ℕ) : k) +
        (8 / 9 : k) * a * e * c * ((4 * n - g : ℕ) : k) -
        (4 / 9 : k) * d ^ 2 * a * ((2 * n : ℕ) : k) +
        (8 / 3 : k) * e ^ 2 * ((6 * n - g : ℕ) : k) = 0) :
    e * (2 * a * c + 3 * e) = 0 := by
  have hw6Nat : 2 * (6 * n - g) = 5 * n := by omega
  have hw4Nat : 2 * (4 * n - g) = n := by omega
  have hw6Cast : (((6 * n - g : ℕ) : k)) =
      (5 / 2 : k) * (n : k) := by
    have hcast : (2 : k) * (((6 * n - g : ℕ) : k)) =
        (5 : k) * (n : k) := by exact_mod_cast hw6Nat
    linear_combination (1 / 2 : k) * hcast
  have hw4Cast : (((4 * n - g : ℕ) : k)) =
      (1 / 2 : k) * (n : k) := by
    have hcast : (2 : k) * (((4 * n - g : ℕ) : k)) = (n : k) := by
      exact_mod_cast hw4Nat
    linear_combination (1 / 2 : k) * hcast
  have htwoCast : (((2 * n : ℕ) : k)) = (2 : k) * (n : k) := by
    norm_num
  rw [hw6Cast, hw4Cast, htwoCast] at hrow
  have hfactor : (20 / 9 : k) * (n : k) *
      (e * (2 * a * c + 3 * e)) = 0 := by
    linear_combination hrow + (8 / 9 : k) * a * (n : k) * hi3
  have hnCast : (n : k) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  exact (mul_eq_zero.mp hfactor).resolve_left
    (mul_ne_zero (by norm_num) hnCast)

set_option maxHeartbeats 10000000 in
/-- Canonical packet on the exact wall `2g=7n`: `B` vanishes, I3 gives the
quadratic `D,c,e` face, I4 ties `D*c` to the `zeta*A` load, and row one
factors into the displayed `e` alternative. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_sevenRadiusWall_packet68
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
      2 * g = 7 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    Be = 0 ∧
      De.coeff (5 * n - g) ^ 2 +
        2 * ce.coeff (4 * n - g) * ee.coeff (6 * n - g) = 0 ∧
      (8 / 3 : k) * De.coeff (5 * n - g) * ce.coeff (4 * n - g) +
        zeta * Ae.coeff (2 * n) = 0 ∧
      ee.coeff (6 * n - g) *
        (2 * Ae.coeff (2 * n) * ce.coeff (4 * n - g) +
          3 * ee.coeff (6 * n - g)) = 0 := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 2 * g = 7 * n at hwall
  change Be = 0 ∧ _ ∧ _ ∧ _
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hn : 0 < n := data.hn
  have hgt3 : 3 * n < 2 * g := by omega
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  obtain ⟨i4, hI4raw⟩ := data.invariant
  have hI4 := hI4raw
  rw [hl, hbeta] at hI4
  have hdelta :=
    cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
      gamma delta epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
      (by omega) data.hA data.hB data.hc data.hD data.he data.ha hI4
  rw [hdelta] at hI4
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hl, hbeta, hdelta] at hi3e
  have hgt6 : 6 * n < 2 * g := by omega
  have hBe :=
    cubicFirstIntegralThreePolynomial68_forces_B_zero_of_sixRadius_lt_twoGap
      gamma epsilon zeta i3 Ae Be ce De ee n g data.hn hgt6
      data.hA data.hB data.hc data.hD data.he data.ha hi3e
  rw [hBe] at hI4 hi3e
  have hface3 := cubicFirstIntegralThreePolynomial68_sixToSeven_face
    gamma epsilon zeta i3 Ae ce De ee n g data.hn
    ⟨hgt6, by omega⟩ data.hA data.hc data.hD data.he hi3e
  have hface4 := cubicFirstIntegralFourPolynomial68_sevenRadiusWall_relation
    gamma epsilon zeta i4 Ae ce De ee n g data.hn hwall
    data.hA data.hc data.hD data.he hI4
  have hrowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hl, hbeta, hdelta, hBe, hCrec, hErec] at hrowOne
  have hrowFace := lowerRowOnePolynomial68_sevenRadiusWall_relation
    alpha gamma epsilon zeta eta Ae ce De ee n g data.hn hwall
    data.hA data.hc data.hD data.he hrowOne
  have heFactor := sevenRadiusWall_i3_rowOne_forces_e_factor68
    n g data.hn hwall
    (Ae.coeff (2 * n)) (ce.coeff (4 * n - g))
    (De.coeff (5 * n - g)) (ee.coeff (6 * n - g)) hface3 hrowFace
  exact ⟨hBe, hface3, hface4, heFactor⟩

end LaterDeepPreclampedLower68

#print axioms lowerRowOnePolynomial68_B_zero_exact
#print axioms cubicFirstIntegralThreePolynomial68_fiveToSix_face
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_invariantFaces68
#print axioms cubicFirstIntegralThreePolynomial68_sixToSeven_face
#print axioms lowerRowOnePolynomial68_sixToSeven_forces_e_top_zero
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_sixToSeven_c_only_top68
#print axioms cubicFirstIntegralFourPolynomial68_c_top_forces_D_degree_drop
#print axioms lowerRowOnePolynomial68_sevenRadiusWall_relation
#print axioms sevenRadiusWall_i3_rowOne_forces_e_factor68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_sevenRadiusWall_packet68

end Max11DegreeRoutes
