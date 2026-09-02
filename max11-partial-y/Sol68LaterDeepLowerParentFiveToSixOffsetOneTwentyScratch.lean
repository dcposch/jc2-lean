import Sol68LaterDeepLowerParentFiveToSixOffsetNinetyScratch

/-! # The offset-one-twenty packet in the five-to-six chamber

The ordinary lane reaches its next leading incidence face.  The aligned
nonzero offset-`60` lane instead sees the first genuine second-jet
convolution.  Fixed-degree reflection packages both calculations without
discarding boundary cases where one of the old bounds is zero.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneTwenty68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The coefficient of order two in a product. -/
theorem mul_coeff_two68 (p q : k[X]) :
    (p * q).coeff 2 =
      p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 +
        p.coeff 2 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]

/-- A coefficient two below a pair of fixed degree bounds, expressed as
the low second jet of the two reflected polynomials. -/
theorem coeff_mul_at_reflect_two68 (p q : k[X]) (u v : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hsum : 2 ≤ u + v) :
    (p * q).coeff (u + v - 2) =
      (p.reflect u).coeff 0 * (q.reflect v).coeff 2 +
        (p.reflect u).coeff 1 * (q.reflect v).coeff 1 +
        (p.reflect u).coeff 2 * (q.reflect v).coeff 0 := by
  have h := congrArg (fun r : k[X] => r.coeff 2)
    (reflect_mul p q hp hq)
  rw [coeff_reflect, revAt_le hsum, mul_coeff_two68] at h
  exact h

/-- Three-factor second jet when the right factor has vanishing reflected
constant term. -/
theorem coeff_mul_mul_at_reflect_two_of_right_zero68
    (p q r : k[X]) (u v w : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hr : r.natDegree ≤ w) (hsum : 2 ≤ u + v + w)
    (hr0 : (r.reflect w).coeff 0 = 0) :
    (p * q * r).coeff (u + v + w - 2) =
      (p.reflect u).coeff 0 * (q.reflect v).coeff 0 *
          (r.reflect w).coeff 2 +
        ((p.reflect u).coeff 0 * (q.reflect v).coeff 1 +
          (p.reflect u).coeff 1 * (q.reflect v).coeff 0) *
            (r.reflect w).coeff 1 := by
  have hpq : (p * q).natDegree ≤ u + v :=
    natDegree_mul_le_of_le hp hq
  have h := congrArg (fun t : k[X] => t.coeff 2)
    (reflect_mul (p * q) r hpq hr)
  rw [coeff_reflect, revAt_le hsum, mul_coeff_two68, hr0, mul_zero,
    add_zero] at h
  rw [reflect_mul p q hp hq, mul_coeff_zero, mul_coeff_one] at h
  exact h

/-- Exact second-jet I4 residual coefficient in the contracted aligned
chart.  The cubic `B` term is already below this coefficient. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_secondJet_fiveToSix
    (B c d e : k[X]) (N G : ℕ) (hG : 2 < G) (hGN : G ≤ 3 * N)
    (hB : B.natDegree ≤ 3 * N - G)
    (hc : c.natDegree ≤ 4 * N - G)
    (hd : d.natDegree ≤ 5 * N - G)
    (he : e.natDegree ≤ 6 * N - G)
    (hd0 : (d.reflect (5 * N - G)).coeff 0 = 0)
    (he0 : (e.reflect (6 * N - G)).coeff 0 = 0) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * N - 2 * G - 2) =
      (8 / 3 : k) *
        ((B.reflect (3 * N - G)).coeff 0 *
            (e.reflect (6 * N - G)).coeff 2 +
          (B.reflect (3 * N - G)).coeff 1 *
            (e.reflect (6 * N - G)).coeff 1 +
          (c.reflect (4 * N - G)).coeff 0 *
            (d.reflect (5 * N - G)).coeff 2 +
          (c.reflect (4 * N - G)).coeff 1 *
            (d.reflect (5 * N - G)).coeff 1) := by
  have hB3 : (B ^ 3).natDegree < 9 * N - 2 * G - 2 := by
    compute_degree
    omega
  have hBe := coeff_mul_at_reflect_two68 B e (3 * N - G)
    (6 * N - G) hB he (by omega)
  have hBei : (3 * N - G) + (6 * N - G) - 2 =
      9 * N - 2 * G - 2 := by omega
  rw [hBei, he0, mul_zero, add_zero] at hBe
  have hcd := coeff_mul_at_reflect_two68 c d (4 * N - G)
    (5 * N - G) hc hd (by omega)
  have hcdi : (4 * N - G) + (5 * N - G) - 2 =
      9 * N - 2 * G - 2 := by omega
  rw [hcdi, hd0, mul_zero, add_zero] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

/-- Exact second-jet I3 residual coefficient.  Besides the next edge pair,
it retains the lower `A,B,c` jets and the first quadratic term `d₆₀²`. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_secondJet_fiveToSix
    (A B c d e : k[X]) (N G : ℕ) (hG : 2 < G) (hGN : G ≤ 3 * N)
    (hA : A.natDegree ≤ 2 * N)
    (hB : B.natDegree ≤ 3 * N - G)
    (hc : c.natDegree ≤ 4 * N - G)
    (hd : d.natDegree ≤ 5 * N - G)
    (he : e.natDegree ≤ 6 * N - G)
    (hd0 : (d.reflect (5 * N - G)).coeff 0 = 0)
    (he0 : (e.reflect (6 * N - G)).coeff 0 = 0) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * N - 2 * G - 2) =
      (8 / 9 : k) *
        (-(A.reflect (2 * N)).coeff 0 *
              (B.reflect (3 * N - G)).coeff 0 *
                (d.reflect (5 * N - G)).coeff 2 -
          ((A.reflect (2 * N)).coeff 0 *
                (B.reflect (3 * N - G)).coeff 1 +
              (A.reflect (2 * N)).coeff 1 *
                (B.reflect (3 * N - G)).coeff 0) *
            (d.reflect (5 * N - G)).coeff 1 +
          3 * (c.reflect (4 * N - G)).coeff 0 *
            (e.reflect (6 * N - G)).coeff 2 +
          3 * (c.reflect (4 * N - G)).coeff 1 *
            (e.reflect (6 * N - G)).coeff 1 +
          (3 / 2 : k) * (d.reflect (5 * N - G)).coeff 1 ^ 2) := by
  have hABd := coeff_mul_mul_at_reflect_two_of_right_zero68 A B d
    (2 * N) (3 * N - G) (5 * N - G) hA hB hd (by omega) hd0
  have hABdi : 2 * N + (3 * N - G) + (5 * N - G) - 2 =
      10 * N - 2 * G - 2 := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 10 * N - 2 * G - 2 := by
    compute_degree
    omega
  have hce := coeff_mul_at_reflect_two68 c e (4 * N - G)
    (6 * N - G) hc he (by omega)
  have hcei : (4 * N - G) + (6 * N - G) - 2 =
      10 * N - 2 * G - 2 := by omega
  rw [hcei, he0, mul_zero, add_zero] at hce
  have hd2 := coeff_mul_at_reflect_two68 d d (5 * N - G)
    (5 * N - G) hd hd (by omega)
  have hd2i : (5 * N - G) + (5 * N - G) - 2 =
      10 * N - 2 * G - 2 := by omega
  rw [hd2i, hd0, zero_mul, mul_zero, zero_add, add_zero] at hd2
  have hd2' : (d ^ 2).coeff (10 * N - 2 * G - 2) =
      (d.reflect (5 * N - G)).coeff 1 ^ 2 := by
    simpa only [pow_two] using hd2
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce, hd2']
  ring

/-- Literal I4 at the aligned second jet.  No lower load is silently
discarded: its exact coefficient is retained in the final three summands. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_secondJet_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X]) (N G : ℕ)
    (hG : 2 < G) (hGN : G ≤ 3 * N)
    (hA : A.natDegree ≤ 2 * N)
    (hB : B.natDegree ≤ 3 * N - G)
    (hc : c.natDegree ≤ 4 * N - G)
    (hd : d.natDegree ≤ 5 * N - G)
    (he : e.natDegree ≤ 6 * N - G)
    (hd0 : (d.reflect (5 * N - G)).coeff 0 = 0)
    (he0 : (e.reflect (6 * N - G)).coeff 0 = 0) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * N - 2 * G - 2) =
      (8 / 3 : k) *
        ((B.reflect (3 * N - G)).coeff 0 *
            (e.reflect (6 * N - G)).coeff 2 +
          (B.reflect (3 * N - G)).coeff 1 *
            (e.reflect (6 * N - G)).coeff 1 +
          (c.reflect (4 * N - G)).coeff 0 *
            (d.reflect (5 * N - G)).coeff 2 +
          (c.reflect (4 * N - G)).coeff 1 *
            (d.reflect (5 * N - G)).coeff 1) +
        zeta * A.coeff (9 * N - 2 * G - 2) +
        2 * epsilon * B.coeff (9 * N - 2 * G - 2) +
        4 * gamma * d.coeff (9 * N - 2 * G - 2) := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_secondJet_fiveToSix
      B c d e N G hG hGN hB hc hd he hd0 he0]
  simp only [coeff_smul, smul_eq_mul]

/-- Literal I3 at the same second jet, including every lower source term.
The residual part is the first occurrence of `d₁²`. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_secondJet_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X]) (N G : ℕ)
    (hG : 2 < G) (hGN : G ≤ 3 * N)
    (hA : A.natDegree ≤ 2 * N)
    (hB : B.natDegree ≤ 3 * N - G)
    (hc : c.natDegree ≤ 4 * N - G)
    (hd : d.natDegree ≤ 5 * N - G)
    (he : e.natDegree ≤ 6 * N - G)
    (hd0 : (d.reflect (5 * N - G)).coeff 0 = 0)
    (he0 : (e.reflect (6 * N - G)).coeff 0 = 0) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * N - 2 * G - 2) =
      (8 / 9 : k) *
        (-(A.reflect (2 * N)).coeff 0 *
              (B.reflect (3 * N - G)).coeff 0 *
                (d.reflect (5 * N - G)).coeff 2 -
          ((A.reflect (2 * N)).coeff 0 *
                (B.reflect (3 * N - G)).coeff 1 +
              (A.reflect (2 * N)).coeff 1 *
                (B.reflect (3 * N - G)).coeff 0) *
            (d.reflect (5 * N - G)).coeff 1 +
          3 * (c.reflect (4 * N - G)).coeff 0 *
            (e.reflect (6 * N - G)).coeff 2 +
          3 * (c.reflect (4 * N - G)).coeff 1 *
            (e.reflect (6 * N - G)).coeff 1 +
          (3 / 2 : k) * (d.reflect (5 * N - G)).coeff 1 ^ 2) +
        zeta * B.coeff (10 * N - 2 * G - 2) +
        2 * epsilon * c.coeff (10 * N - 2 * G - 2) +
        4 * gamma * e.coeff (10 * N - 2 * G - 2) -
        (2 / 3 * gamma : k) * (B ^ 2).coeff (10 * N - 2 * G - 2) := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    coeff_sub, coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_secondJet_fiveToSix
      A B c d e N G hG hGN hA hB hc hd he hd0 he0]
  simp only [coeff_smul, smul_eq_mul]

/-- The singular second-jet system has one exact compatibility scalar.
The right side is precisely the surviving I4 load. -/
theorem fiveToSix_secondJet_discriminant_compatibility68
    (a a₁ b b₁ c c₁ x y u v L M : k)
    (hb : b ≠ 0)
    (hfour0 : b * y + c * x = 0)
    (hdisc : a * b ^ 2 + 3 * c ^ 2 = 0)
    (hfour : (8 / 3 : k) * (b * v + b₁ * y + c * u + c₁ * x) + L = 0)
    (hthree : -a * b * u - (a * b₁ + a₁ * b) * x +
        3 * c * v + 3 * c₁ * y + (3 / 2 : k) * x ^ 2 + M = 0) :
    4 * x * (3 * b * x - 2 * a₁ * b ^ 2 - 4 * a * b * b₁ -
        12 * c * c₁) = 9 * c * L - 8 * b * M := by
  have hcompat :
      b * (4 * x * (3 * b * x - 2 * a₁ * b ^ 2 -
        4 * a * b * b₁ - 12 * c * c₁) - 9 * c * L + 8 * b * M) = 0 := by
    linear_combination 8 * b ^ 2 * hthree - 9 * b * c * hfour +
      8 * b * u * hdisc - 24 * b * c₁ * hfour0 +
      24 * c * b₁ * hfour0 - 8 * b₁ * x * hdisc
  have hzero :
      4 * x * (3 * b * x - 2 * a₁ * b ^ 2 -
        4 * a * b * b₁ - 12 * c * c₁) - 9 * c * L + 8 * b * M = 0 :=
    (mul_eq_zero.mp hcompat).resolve_left hb
  linear_combination hzero

set_option maxHeartbeats 8000000 in
/-- Exact source-facing aligned offset-`120` packet.  The old singular face
turns the two literal first-integral coefficients into one compatibility
identity.  `L` and `M` are the complete lower-source loads, so the small
`(N,G)=(1,3)` chart and the ordinary `(2,6)` load wall remain visible. -/
theorem fiveToSix_aligned_secondJet_source_packet68
    (gamma epsilon zeta i4 i3 : k) (A B c d e : k[X]) (N G : ℕ)
    (hG : 2 < G) (hGN : G ≤ 3 * N)
    (hA : A.natDegree ≤ 2 * N)
    (hB : B.natDegree ≤ 3 * N - G)
    (hc : c.natDegree ≤ 4 * N - G)
    (hd : d.natDegree ≤ 5 * N - G)
    (he : e.natDegree ≤ 6 * N - G)
    (hd0 : (d.reflect (5 * N - G)).coeff 0 = 0)
    (he0 : (e.reflect (6 * N - G)).coeff 0 = 0)
    (hb : (B.reflect (3 * N - G)).coeff 0 ≠ 0)
    (hface :
      (B.reflect (3 * N - G)).coeff 0 *
          (e.reflect (6 * N - G)).coeff 1 +
        (c.reflect (4 * N - G)).coeff 0 *
          (d.reflect (5 * N - G)).coeff 1 = 0)
    (hdisc :
      (A.reflect (2 * N)).coeff 0 *
          (B.reflect (3 * N - G)).coeff 0 ^ 2 +
        3 * (c.reflect (4 * N - G)).coeff 0 ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    let a := (A.reflect (2 * N)).coeff 0
    let a₁ := (A.reflect (2 * N)).coeff 1
    let b := (B.reflect (3 * N - G)).coeff 0
    let b₁ := (B.reflect (3 * N - G)).coeff 1
    let c₀ := (c.reflect (4 * N - G)).coeff 0
    let c₁ := (c.reflect (4 * N - G)).coeff 1
    let x := (d.reflect (5 * N - G)).coeff 1
    let y := (e.reflect (6 * N - G)).coeff 1
    let u := (d.reflect (5 * N - G)).coeff 2
    let v := (e.reflect (6 * N - G)).coeff 2
    let L := zeta * A.coeff (9 * N - 2 * G - 2) +
      2 * epsilon * B.coeff (9 * N - 2 * G - 2) +
      4 * gamma * d.coeff (9 * N - 2 * G - 2)
    let M := (9 / 8 : k) *
      (zeta * B.coeff (10 * N - 2 * G - 2) +
        2 * epsilon * c.coeff (10 * N - 2 * G - 2) +
        4 * gamma * e.coeff (10 * N - 2 * G - 2) -
        (2 / 3 * gamma : k) * (B ^ 2).coeff (10 * N - 2 * G - 2))
    ((8 / 3 : k) * (b * v + b₁ * y + c₀ * u + c₁ * x) + L = 0) ∧
      (-a * b * u - (a * b₁ + a₁ * b) * x + 3 * c₀ * v +
        3 * c₁ * y + (3 / 2 : k) * x ^ 2 + M = 0) ∧
      4 * x * (3 * b * x - 2 * a₁ * b ^ 2 - 4 * a * b * b₁ -
        12 * c₀ * c₁) = 9 * c₀ * L - 8 * b * M := by
  dsimp only
  have hj4 : 9 * N - 2 * G - 2 ≠ 0 := by omega
  have hj3 : 10 * N - 2 * G - 2 ≠ 0 := by omega
  have hcoeff4 := congrArg
    (fun p : k[X] => p.coeff (9 * N - 2 * G - 2)) hi4
  rw [cubicFirstIntegralFourPolynomial68_coeff_secondJet_fiveToSix
    gamma epsilon zeta A B c d e N G hG hGN hA hB hc hd he hd0 he0]
      at hcoeff4
  simp only [coeff_C, if_neg hj4] at hcoeff4
  have hfour :
      (8 / 3 : k) *
          ((B.reflect (3 * N - G)).coeff 0 *
              (e.reflect (6 * N - G)).coeff 2 +
            (B.reflect (3 * N - G)).coeff 1 *
              (e.reflect (6 * N - G)).coeff 1 +
            (c.reflect (4 * N - G)).coeff 0 *
              (d.reflect (5 * N - G)).coeff 2 +
            (c.reflect (4 * N - G)).coeff 1 *
              (d.reflect (5 * N - G)).coeff 1) +
        (zeta * A.coeff (9 * N - 2 * G - 2) +
          2 * epsilon * B.coeff (9 * N - 2 * G - 2) +
          4 * gamma * d.coeff (9 * N - 2 * G - 2)) = 0 := by
    linear_combination hcoeff4
  have hcoeff3 := congrArg
    (fun p : k[X] => p.coeff (10 * N - 2 * G - 2)) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_secondJet_fiveToSix
    gamma epsilon zeta A B c d e N G hG hGN hA hB hc hd he hd0 he0]
      at hcoeff3
  simp only [coeff_C, if_neg hj3] at hcoeff3
  have hthree :
      -(A.reflect (2 * N)).coeff 0 *
            (B.reflect (3 * N - G)).coeff 0 *
              (d.reflect (5 * N - G)).coeff 2 -
        ((A.reflect (2 * N)).coeff 0 *
              (B.reflect (3 * N - G)).coeff 1 +
            (A.reflect (2 * N)).coeff 1 *
              (B.reflect (3 * N - G)).coeff 0) *
          (d.reflect (5 * N - G)).coeff 1 +
        3 * (c.reflect (4 * N - G)).coeff 0 *
          (e.reflect (6 * N - G)).coeff 2 +
        3 * (c.reflect (4 * N - G)).coeff 1 *
          (e.reflect (6 * N - G)).coeff 1 +
        (3 / 2 : k) * (d.reflect (5 * N - G)).coeff 1 ^ 2 +
        (9 / 8 : k) *
          (zeta * B.coeff (10 * N - 2 * G - 2) +
            2 * epsilon * c.coeff (10 * N - 2 * G - 2) +
            4 * gamma * e.coeff (10 * N - 2 * G - 2) -
            (2 / 3 * gamma : k) *
              (B ^ 2).coeff (10 * N - 2 * G - 2)) = 0 := by
    linear_combination (9 / 8 : k) * hcoeff3
  refine ⟨hfour, hthree, ?_⟩
  exact fiveToSix_secondJet_discriminant_compatibility68
    (a := (A.reflect (2 * N)).coeff 0)
    (a₁ := (A.reflect (2 * N)).coeff 1)
    (b := (B.reflect (3 * N - G)).coeff 0)
    (b₁ := (B.reflect (3 * N - G)).coeff 1)
    (c := (c.reflect (4 * N - G)).coeff 0)
    (c₁ := (c.reflect (4 * N - G)).coeff 1)
    (x := (d.reflect (5 * N - G)).coeff 1)
    (y := (e.reflect (6 * N - G)).coeff 1)
    (u := (d.reflect (5 * N - G)).coeff 2)
    (v := (e.reflect (6 * N - G)).coeff 2)
    (L := zeta * A.coeff (9 * N - 2 * G - 2) +
      2 * epsilon * B.coeff (9 * N - 2 * G - 2) +
      4 * gamma * d.coeff (9 * N - 2 * G - 2))
    (M := (9 / 8 : k) *
      (zeta * B.coeff (10 * N - 2 * G - 2) +
        2 * epsilon * c.coeff (10 * N - 2 * G - 2) +
        4 * gamma * e.coeff (10 * N - 2 * G - 2) -
        (2 / 3 * gamma : k) * (B ^ 2).coeff (10 * N - 2 * G - 2)))
    hb hface hdisc hfour hthree

/-- The ordinary offset-`120` I4 face. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_gap_oneTwenty_fiveToSix
    (B c d e : k[X]) (n g : ℕ) (hn : 60 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 120)
    (he : e.natDegree ≤ 6 * n - g - 120) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 2 * g - 120) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 120) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 120)) := by
  have hB3 : (B ^ 3).natDegree < 9 * n - 2 * g - 120 := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g)
    (6 * n - g - 120) hB he
  have hBei : (3 * n - g) + (6 * n - g - 120) =
      9 * n - 2 * g - 120 := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g)
    (5 * n - g - 120) hc hd
  have hcdi : (4 * n - g) + (5 * n - g - 120) =
      9 * n - 2 * g - 120 := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

/-- Literal ordinary I4, retaining its possible `zeta*A` load. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_gap_oneTwenty_loaded_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 60 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 120)
    (he : e.natDegree ≤ 6 * n - g - 120) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - 2 * g - 120) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 120) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 120)) +
        zeta * A.coeff (9 * n - 2 * g - 120) := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_gap_oneTwenty_fiveToSix
      B c d e n g hn hwindow hB hc hd he]
  have hloadB : ((2 * epsilon : k) • B).natDegree <
      9 * n - 2 * g - 120 := by compute_degree; omega
  have hloadd : ((4 * gamma : k) • d).natDegree <
      9 * n - 2 * g - 120 := by compute_degree; omega
  rw [coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd]
  simp only [coeff_smul, smul_eq_mul]
  ring

/-- I3 is load-free on the ordinary offset-`120` face. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_gap_oneTwenty_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 60 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 120)
    (he : e.natDegree ≤ 6 * n - g - 120) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - 2 * g - 120) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - g - 120)) +
          3 * c.coeff (4 * n - g) *
            e.coeff (6 * n - g - 120)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - g - 120) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - g - 120) =
      10 * n - 2 * g - 120 := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 10 * n - 2 * g - 120 := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g)
    (6 * n - g - 120) hc he
  have hcei : (4 * n - g) + (6 * n - g - 120) =
      10 * n - 2 * g - 120 := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 2 * g - 120 := by
    compute_degree
    omega
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    coeff_sub, coeff_add, coeff_add, coeff_add]
  have hloadB : (zeta • B).natDegree < 10 * n - 2 * g - 120 := by
    compute_degree
    omega
  have hloadc : ((2 * epsilon : k) • c).natDegree <
      10 * n - 2 * g - 120 := by compute_degree; omega
  have hloade : ((4 * gamma : k) • e).natDegree <
      10 * n - 2 * g - 120 := by compute_degree; omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree <
      10 * n - 2 * g - 120 := by compute_degree; omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2,
    coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2]
  ring

/-- The homogeneous row-zero coefficient on the ordinary offset-`120`
face. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_gap_oneTwenty_fiveToSix
    (A B c d e : k[X]) (n g : ℕ) (hn : 60 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 120)
    (he : e.natDegree ≤ 6 * n - g - 120) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 2 * g - 121) =
      (-8 / 27 : k) * (n : k) * A.coeff (2 * n) ^ 2 *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 120) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 120)) := by
  have h1raw := coeff_mul_mul_mul_derivative_at_bounds68 A B e A
    (2 * n) (3 * n - g) (6 * n - g - 120) (2 * n) (by omega)
    hA hB he hA
  have hi1 : 2 * n + (3 * n - g) + (6 * n - g - 120) + 2 * n - 1 =
      13 * n - 2 * g - 121 := by omega
  rw [hi1] at h1raw
  have h1 : (A * derivative A * B * e).coeff
      (13 * n - 2 * g - 121) =
      A.coeff (2 * n) * A.coeff (2 * n) *
        B.coeff (3 * n - g) * e.coeff (6 * n - g - 120) *
          (((2 * n : ℕ) : k)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1raw
  have h2raw := coeff_mul_mul_mul_derivative_at_bounds68 A c d A
    (2 * n) (4 * n - g) (5 * n - g - 120) (2 * n) (by omega)
    hA hc hd hA
  have hi2 : 2 * n + (4 * n - g) + (5 * n - g - 120) + 2 * n - 1 =
      13 * n - 2 * g - 121 := by omega
  rw [hi2] at h2raw
  have h2 : (A * derivative A * c * d).coeff
      (13 * n - 2 * g - 121) =
      A.coeff (2 * n) * A.coeff (2 * n) *
        c.coeff (4 * n - g) * d.coeff (5 * n - g - 120) *
          (((2 * n : ℕ) : k)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2raw
  have hlow1 : (A * B ^ 2 * derivative d).natDegree <
      13 * n - 2 * g - 121 := by compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree <
      13 * n - 2 * g - 121 := by compute_degree; omega
  have hlow3 : (derivative A * B * c ^ 2).natDegree <
      13 * n - 2 * g - 121 := by compute_degree; omega
  have hlow4 : (derivative A * d * e).natDegree <
      13 * n - 2 * g - 121 := by compute_degree; omega
  have hlow5 : (B * c * derivative e).natDegree <
      13 * n - 2 * g - 121 := by compute_degree; omega
  have hlow6 : (B * d * derivative d).natDegree <
      13 * n - 2 * g - 121 := by compute_degree; omega
  have hlow7 : (derivative B * d ^ 2).natDegree <
      13 * n - 2 * g - 121 := by compute_degree; omega
  have hlow8 : (c * derivative c * d).natDegree <
      13 * n - 2 * g - 121 := by compute_degree; omega
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8, smul_eq_mul]
  push_cast
  ring

/-- The prospective ordinary load wall is exactly `(n,g)=(120,360)`.
Its literal I4 and row-zero coefficients force `zeta=0`; no coefficient of
the residual edge pair is divided away. -/
theorem fiveToSix_offsetOneTwenty_wall_source_zeta_zero68
    (alpha gamma epsilon zeta eta i4 i3 : k) (A B c d e : k[X])
    (ha : A.coeff 240 ≠ 0)
    (hb : B.coeff 0 ≠ 0)
    (hA : A.natDegree ≤ 240) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 120) (hd : d.natDegree ≤ 120)
    (he : e.natDegree ≤ 240)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow : (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 719 = 0) :
    zeta = 0 ∧
      ((d.coeff 120 = 0 ∧ e.coeff 240 = 0) ∨
        (B.coeff 0 ≠ 0 ∧ c.coeff 120 ≠ 0 ∧
          d.coeff 120 ≠ 0 ∧ e.coeff 240 ≠ 0 ∧
          A.coeff 240 * B.coeff 0 ^ 2 + 3 * c.coeff 120 ^ 2 = 0)) := by
  have hcoeff4 := congrArg (fun p : k[X] => p.coeff 240) hi4
  rw [cubicFirstIntegralFourPolynomial68_coeff_gap_oneTwenty_loaded_fiveToSix
    gamma epsilon zeta A B c d e 120 360 (by norm_num)
    (by norm_num) hA hB hc hd he] at hcoeff4
  norm_num [coeff_C] at hcoeff4
  have hres :=
    secondaryResidualRowZeroPolynomial68_coeff_gap_oneTwenty_fiveToSix
      A B c d e 120 360 (by norm_num) (by norm_num) hA hB hc hd he
  norm_num at hres
  have hload := cubicLoadRowZeroPolynomial68_coeff_constantB_chart68
    alpha gamma epsilon zeta eta A B c d e 120 (by norm_num)
    hA hB hc hd he
  norm_num at hload
  rw [coeff_add, hres, hload] at hrow
  have hzetaCube : zeta * A.coeff 240 ^ 3 = 0 := by
    linear_combination (1 / 40 : k) * hrow +
      (1 / 3 : k) * A.coeff 240 ^ 2 * hcoeff4
  have hzeta : zeta = 0 :=
    (mul_eq_zero.mp hzetaCube).resolve_right (pow_ne_zero 3 ha)
  have hfour : B.coeff 0 * e.coeff 240 +
      c.coeff 120 * d.coeff 120 = 0 := by
    rw [hzeta, zero_mul, add_zero] at hcoeff4
    exact (mul_eq_zero.mp hcoeff4).resolve_left (by norm_num)
  have hcoeff3 := congrArg (fun p : k[X] => p.coeff 360) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_gap_oneTwenty_fiveToSix
    gamma epsilon zeta A B c d e 120 360 (by norm_num)
    (by norm_num) hA hB hc hd he] at hcoeff3
  norm_num [coeff_C] at hcoeff3
  have hthree : -A.coeff 240 * B.coeff 0 * d.coeff 120 +
      3 * c.coeff 120 * e.coeff 240 = 0 := by
    linear_combination hcoeff3
  have hface : SecondaryResidualBetweenFace68
      (A.coeff 240) (B.coeff 0) (c.coeff 120)
      (d.coeff 120) (e.coeff 240) := ⟨hfour, hthree⟩
  refine ⟨hzeta, ?_⟩
  by_cases hedge : d.coeff 120 = 0 ∧ e.coeff 240 = 0
  · exact Or.inl hedge
  · right
    have hattained : d.coeff 120 ≠ 0 ∨ e.coeff 240 ≠ 0 := by tauto
    exact secondaryResidualBetweenFace68_classify_of_support
      (A.coeff 240) (B.coeff 0) (c.coeff 120)
      (d.coeff 120) (e.coeff 240) ha (Or.inl hb) hattained hface

#print axioms mul_coeff_two68
#print axioms coeff_mul_at_reflect_two68
#print axioms coeff_mul_mul_at_reflect_two_of_right_zero68
#print axioms secondaryResidualInvariantFourPolynomial68_coeff_secondJet_fiveToSix
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_secondJet_fiveToSix
#print axioms cubicFirstIntegralFourPolynomial68_coeff_secondJet_fiveToSix
#print axioms cubicFirstIntegralThreePolynomial68_coeff_secondJet_fiveToSix
#print axioms fiveToSix_secondJet_discriminant_compatibility68
#print axioms fiveToSix_aligned_secondJet_source_packet68
#print axioms secondaryResidualInvariantFourPolynomial68_coeff_gap_oneTwenty_fiveToSix
#print axioms cubicFirstIntegralFourPolynomial68_coeff_gap_oneTwenty_loaded_fiveToSix
#print axioms cubicFirstIntegralThreePolynomial68_coeff_gap_oneTwenty_fiveToSix
#print axioms secondaryResidualRowZeroPolynomial68_coeff_gap_oneTwenty_fiveToSix
#print axioms fiveToSix_offsetOneTwenty_wall_source_zeta_zero68

end LaterDeepLowerParentFiveToSixOffsetOneTwenty68

end Max11DegreeRoutes
