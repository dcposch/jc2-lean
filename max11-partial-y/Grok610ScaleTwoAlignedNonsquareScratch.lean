import Grok610AlignedSquareFinalRowScratch

/-! # Transverse `g₁`-root kill on the aligned-nonsquare `(6,10)` chamber

Untracked working note.  No tracked file was edited.

`Grok610AlignedSquareFinalRowScratch` recorded the aligned-nonsquare
open packet: the eleventh-face jet together with the carried residue
`alignedEleventhNonsquareResidue610 = 0`, the chamber-free degree-`3`
row `alignedTwelfthJacobianRow610 p q = 0`, and the inhomogeneous
Keller row `p₀' q₁ - p₁ q₀' = C j`.  The unused objects on this
chamber were the degree-`2` and degree-`1` Jacobian coefficients
together with that residue.

This file attaches both remaining Jacobian coefficients (they are
chamber-free coefficient identities of the original Keller bracket)
and runs the `(4,10)` transverse elimination pattern
`normalized410ScaleTwo_alignedNonsquare_false` against the carried
nonsquare jet.  The ninth solved block
`alignedNinthNonsquareSolved610` vanishes at any root of `H` where
`g₁` vanishes, so `q₁` vanishes there; the tenth-face divisor
`243 p₁ - g₁ u = H v` forces `p₁` to vanish at the same root.  The
Keller row therefore evaluates to `0 = j`, contradicting `j ≠ 0`.

Consequently `g₁` vanishes at no root of the quadratic core: the
`(4,10)` `H ∣ g` limb and every transverse `g = 0` orientation are
killed in one step.  The complementary limb `g₁(a) ≠ 0` at both simple
roots is **not closed**.  On that limb the residue remains a live
`p₀`-loaded relation, and the next unused constraint is the degree-`1`
Jacobian coefficient evaluated at a root of `H` after cancelling the
forced `g₁` factor (`alignedNonsquareDegreeOneRootHead610`).

The peel lemmas `alignedNonsquare_dvd_p5_610`,
`alignedNonsquareThird_solved_610`, `alignedNonsquareSixth_solved_610`,
and `alignedNonsquareEleventh_descent_610` are reused through the
eleventh-face nonsquare packet / chamber dichotomy.  No total-degree
or twice-prime theorem is used.  No `sorry`, no new axioms, no
finite-root shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 1000000

/-! ## Literal unused Jacobian coefficients -/

/-- The literal degree-`2` coefficient of the `(6,10)` Keller Jacobian.
Its antidiagonal is `(0,3),(1,2),(2,1)` before taking the `y`-derivative. -/
def alignedThirteenthJacobianRow610 {K : Type*} [CommRing K]
    (p q : K[X][Y]) : K[X] :=
  (p.coeff 2).derivative * q.coeff 1 +
      (p.coeff 1).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
      (p.coeff 0).derivative * (q.coeff 3 * Polynomial.C (3 : K)) -
    ((p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 0).derivative +
      (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 1).derivative +
      p.coeff 1 * (q.coeff 2).derivative)

/-- The literal degree-`1` coefficient of the `(6,10)` Keller Jacobian.
Its antidiagonal is `(0,2),(1,1)` before taking the `y`-derivative. -/
def alignedFourteenthJacobianRow610 {K : Type*} [CommRing K]
    (p q : K[X][Y]) : K[X] :=
  (p.coeff 1).derivative * q.coeff 1 +
      (p.coeff 0).derivative * (q.coeff 2 * Polynomial.C (2 : K)) -
    ((p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 0).derivative +
      p.coeff 1 * (q.coeff 1).derivative)

theorem alignedThirteenthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    alignedThirteenthJacobianRow610 p q = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 2) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (2 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 2 :
      Finset (ℕ × ℕ)) =
      ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)) := by
    decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff
  simp only [alignedThirteenthJacobianRow610]
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  rw [hC2, hC3]
  linear_combination hcoeff

theorem alignedFourteenthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    alignedFourteenthJacobianRow610 p q = 0 := by
  simpa only [alignedFourteenthJacobianRow610] using
    alignedFourteenthSquareCoefficientJacobianRow_610 hp hq hjac

/-- `g₁`-cancelled algebraic head of `q₁` at a root of `H`.  After the
carried substitutions `t₂(a) = 6 g₁(a) t₁(a)` and
`243 p₁(a) = g₁(a) u(a)`, CAS gives
`45349632 q₁(a) = g₁(a) · alignedNonsquareDegreeOneRootHead610(a)`.
This is the next unused constraint on the complementary `g₁(a) ≠ 0`
limb, to be paired with the degree-`1` Jacobian at the same root. -/
def alignedNonsquareDegreeOneRootHead610 {K : Type*} [CommRing K]
    (a0 t1 u : K[X]) (κ κ₃ κ₅ κ₇ : K) : K[X] :=
  (2239488 : K[X]) * a0 * Polynomial.C κ +
      (5598720 : K[X]) * a0 * t1 -
    Polynomial.C κ₃ * ((384 : K[X]) * u) -
    Polynomial.C κ₅ * ((32 : K[X]) * t1) -
    Polynomial.C κ₇ -
    Polynomial.C κ * ((3072 : K[X]) * t1 ^ 3) +
    Polynomial.C κ * ((3072 : K[X]) * t1 * u) +
    (3840 : K[X]) * t1 ^ 4 -
    (3840 : K[X]) * t1 ^ 2 * u +
    (1280 : K[X]) * u ^ 2

/-! ## Ninth-block vanishing at a `g₁ = 0` root -/

variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 8000000 in
/-- Polynomial identity used only through evaluation: every
`H`-free term of the ninth solved block is linear in `(g₁, t₂, p₁)`. -/
theorem alignedNinthNonsquareSolved_g1_t2_a1_zero_610
    (H t1 u t3 a0 : K[X]) (κ κ₃ κ₅ κ₇ : K) :
    alignedNinthNonsquareSolved610 H 0 t1 0 u t3 a0 0 κ κ₃ κ₅ κ₇ =
      H ^ 2 * (-(5120 : K[X]) * t3 ^ 3) := by
  simp only [alignedNinthNonsquareSolved610]
  ring

set_option maxHeartbeats 8000000 in
/-- At a root of `H` where `g₁`, `t₂`, and `p₁` vanish, the ninth
solved block vanishes. -/
theorem alignedNinthNonsquareSolved_eval_g1_zero_610
    (H g1 t1 t2 u t3 a0 a1 : K[X]) (κ κ₃ κ₅ κ₇ : K)
    (x : K) (hx : H.eval x = 0) (hg : g1.eval x = 0)
    (ht2 : t2.eval x = 0) (ha1 : a1.eval x = 0) :
    (alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 a0 a1
        κ κ₃ κ₅ κ₇).eval x = 0 := by
  simp only [alignedNinthNonsquareSolved610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
  rw [hx, hg, ht2, ha1]
  norm_num

/-! ## Source-facing `g₁`-root kill -/

variable [IsAlgClosed K]

set_option maxHeartbeats 16000000 in
/-- The ninth solved block together with the tenth-face `p₁` divisor
force both Keller factors to vanish at a `g₁ = 0` root of `H`. -/
theorem alignedNonsquare_g1Root_forces_q1_p1_zero_610
    {H g1 t1 t2 u t3 v a0 a1 b1 : K[X]} {κ κ₃ κ₅ κ₇ : K}
    (ht3 : t2 - (6 : K[X]) * g1 * t1 = H * t3)
    (hv : (243 : K[X]) * a1 - g1 * u = H * v)
    (hq1 : (1632586752 : K[X]) * b1 =
      alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 a0 a1 κ κ₃ κ₅ κ₇)
    (x : K) (hx : H.eval x = 0) (hgx : g1.eval x = 0) :
    a1.eval x = 0 ∧ b1.eval x = 0 := by
  have ht2x : t2.eval x = 0 := by
    have hev := congrArg (fun w : K[X] => w.eval x) ht3
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_ofNat] at hev
    rw [hx, hgx] at hev
    linear_combination hev
  have ha1x : a1.eval x = 0 := by
    have hev := congrArg (fun w : K[X] => w.eval x) hv
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_ofNat] at hev
    rw [hx, hgx] at hev
    have h243 : (243 : K) * a1.eval x = 0 := by
      linear_combination hev
    exact (mul_eq_zero.mp h243).resolve_left
      (by norm_num : (243 : K) ≠ 0)
  have hblockx :=
    alignedNinthNonsquareSolved_eval_g1_zero_610 H g1 t1 t2 u t3 a0 a1
      κ κ₃ κ₅ κ₇ x hx hgx ht2x ha1x
  have hb1x : b1.eval x = 0 := by
    have hev := congrArg (fun w : K[X] => w.eval x) hq1
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
    rw [hblockx] at hev
    exact (mul_eq_zero.mp hev).resolve_left
      (by norm_num : (1632586752 : K) ≠ 0)
  exact ⟨ha1x, hb1x⟩

set_option maxHeartbeats 16000000 in
/-- Every nonsquare aligned scale-two `(6,10)` source is impossible at a
root of `H` where the carried witness `g₁` vanishes: both Keller
factors die and the original constant `j` is forced to zero. -/
theorem normalized610ScaleTwo_alignedNonsquare_g1Root_false
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (x : K) (hx : H.eval x = 0)
    {g1 : K[X]}
    (hgx :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      ∃ (κ κ₃ κ₅ κ₇ κ₉ : K) (f t1 t2 u t3 v : K[X]),
        p.coeff 5 = H ^ 2 * g1 ∧
          g1.eval x = 0 ∧
            (1632586752 : K[X]) *
                ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 1 =
              alignedNinthNonsquareSolved610 H g1 t1 t2 u t3
                (p.coeff 0) (p.coeff 1) κ κ₃ κ₅ κ₇ ∧
              t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧
                (243 : K[X]) * p.coeff 1 - g1 * u = H * v) :
    False := by
  dsimp only at haligned hgx
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨_κ, _κ₃, _κ₅, _κ₇, _κ₉, _f, t1, t2, u, t3, v, _hp5, hgx',
    hq1, ht3, hv⟩ := hgx
  obtain ⟨hp1x, hq1x⟩ :=
    alignedNonsquare_g1Root_forces_q1_p1_zero_610 ht3 hv hq1 x hx hgx'
  obtain ⟨j, hj, hrow⟩ :=
    normalized610ScaleTwo_alignedFinalKellerRow hsource haligned
  have hev := congrArg (fun w : K[X] => w.eval x) hrow
  simp only [p, q, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C] at hev
  rw [hp1x, hq1x] at hev
  simp only [mul_zero, zero_mul, sub_zero] at hev
  exact hj hev.symm

set_option maxHeartbeats 16000000 in
/-- Source-facing `g₁`-root exclusion: the eleventh-face nonsquare
packet supplies the ninth solved block and the `p₁` divisor, so `g₁`
vanishes at no root of `H`. -/
theorem normalized610ScaleTwo_alignedNonsquare_g1_ne_zero_atRoot
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    ∃ (κ κ₃ κ₅ κ₇ κ₉ : K) (g1 f t1 t2 u t3 v : K[X]),
      p.coeff 5 = H ^ 2 * g1 ∧
        p.coeff 4 = H * f ∧
        (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
        (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
        (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 =
          H * u ∧
        t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧
        (243 : K[X]) * p.coeff 1 - g1 * u = H * v ∧
        alignedEleventhNonsquareResidue610 H g1 t1 u t3 v (p.coeff 0)
            κ κ₅ κ₇ = 0 ∧
          ∀ x : K, H.eval x = 0 → g1.eval x ≠ 0 := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, f, t1, t2, u, t3, v, _hM, hp5, hf,
    ht1, ht2, hu, ht3, hv, _hq0, hq1, _hq2, _hD0, _hE, _hF0, _hG,
    _hI0, _hJ, _hL0, _hO, _hΛ0, hres⟩ :=
    normalized610ScaleTwo_alignedEleventhFace_nonsquareChamber_packet
      hsource hnsq haligned
  refine ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, f, t1, t2, u, t3, v, hp5, hf, ht1,
    ht2, hu, ht3, hv, hres, ?_⟩
  intro x hx hgx
  exact normalized610ScaleTwo_alignedNonsquare_g1Root_false
    hsource hnsq haligned x hx
    ⟨κ, κ₃, κ₅, κ₇, κ₉, f, t1, t2, u, t3, v, hp5, hgx, hq1, ht3, hv⟩

set_option maxHeartbeats 16000000 in
/-- Residual packet of the aligned nonsquare chamber.  Both remaining
Jacobian coefficients are attached, the residue is retained, and the
`g₁ = 0` root allocation is excluded.  The complementary limb
`g₁(a) ≠ 0` is not closed: the next unused constraint is the named
degree-`1` head `alignedNonsquareDegreeOneRootHead610` against the
degree-`1` Jacobian at a root of `H`.  No `False` is claimed. -/
theorem normalized610ScaleTwo_alignedNonsquare_residualPacket
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    (∃ (κ κ₃ κ₅ κ₇ κ₉ : K) (g1 f t1 t2 u t3 v : K[X]),
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
        p.coeff 5 = H ^ 2 * g1 ∧ p.coeff 4 = H * f ∧
        (3 : K[X]) * f - g1 ^ 2 = H * t1 ∧
        (27 : K[X]) * p.coeff 3 - g1 ^ 3 = H * t2 ∧
        (81 : K[X]) * p.coeff 2 + (3 : K[X]) * g1 ^ 2 * t1 - g1 * t2 =
          H * u ∧
        t2 - (6 : K[X]) * g1 * t1 = H * t3 ∧
        (243 : K[X]) * p.coeff 1 - g1 * u = H * v ∧
        alignedEleventhNonsquareResidue610 H g1 t1 u t3 v (p.coeff 0)
            κ κ₅ κ₇ = 0 ∧
          ∀ x : K, H.eval x = 0 → g1.eval x ≠ 0) ∧
      (∃ j : K, j ≠ 0 ∧
        bivariateJacobian p q = Polynomial.C (Polynomial.C j) ∧
          alignedTwelfthJacobianRow610 p q = 0 ∧
          alignedThirteenthJacobianRow610 p q = 0 ∧
          alignedFourteenthJacobianRow610 p q = 0 ∧
          (p.coeff 0).derivative * q.coeff 1 -
              p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j) := by
  dsimp only at haligned ⊢
  refine ⟨?jet, ?rows⟩
  · let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, f, t1, t2, u, t3, v, hM, hp5, hf,
      ht1, ht2, hu, ht3, hv, _hq0, hq1, _hq2, _hD0, _hE, _hF0, _hG,
      _hI0, _hJ, _hL0, _hO, _hΛ0, hres⟩ :=
      normalized610ScaleTwo_alignedEleventhFace_nonsquareChamber_packet
        hsource hnsq haligned
    refine ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, f, t1, t2, u, t3, v, hM, hp5, hf,
      ht1, ht2, hu, ht3, hv, hres, ?_⟩
    intro x hx hgx
    exact normalized610ScaleTwo_alignedNonsquare_g1Root_false
      hsource hnsq haligned x hx
      ⟨κ, κ₃, κ₅, κ₇, κ₉, f, t1, t2, u, t3, v, hp5, hgx, hq1, ht3, hv⟩
  · rcases hsource with
      ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp6, _hq10, hKeller⟩
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
    have hp : p.natDegree = 6 := by
      simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
    have hq : q.natDegree = 10 := by
      simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
    have hD : GCD369SourceXDeriv p * derivative q -
        derivative p * GCD369SourceXDeriv q =
          Polynomial.C (Polynomial.C j) := by
      simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv]
        using hjac
    exact ⟨j, hj, hjac,
      alignedTwelfthCoefficientJacobianRow_610 hp hq hjac,
      alignedThirteenthCoefficientJacobianRow_610 hp hq hjac,
      alignedFourteenthCoefficientJacobianRow_610 hp hq hjac,
      source610_degreeZeroJacobianRow p q j hD⟩

#print axioms alignedThirteenthCoefficientJacobianRow_610
#print axioms alignedFourteenthCoefficientJacobianRow_610
#print axioms alignedNinthNonsquareSolved_g1_t2_a1_zero_610
#print axioms alignedNinthNonsquareSolved_eval_g1_zero_610
#print axioms alignedNonsquare_g1Root_forces_q1_p1_zero_610
#print axioms normalized610ScaleTwo_alignedNonsquare_g1Root_false
#print axioms normalized610ScaleTwo_alignedNonsquare_g1_ne_zero_atRoot
#print axioms normalized610ScaleTwo_alignedNonsquare_residualPacket

end Max11DegreeRoutes
