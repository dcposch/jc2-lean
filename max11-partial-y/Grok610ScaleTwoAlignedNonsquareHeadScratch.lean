import Grok610ScaleTwoAlignedNonsquareScratch

/-! # Complementary `g₁ ≠ 0` head of the aligned-nonsquare `(6,10)` chamber

Untracked working note.  No tracked file was edited.

`Grok610ScaleTwoAlignedNonsquareScratch` killed the transverse limb
`g₁(a) = 0` at any root of the quadratic core and recorded the residual
packet on the complementary limb `g₁(a) ≠ 0` at both simple roots, with
the degree-`2` and degree-`1` Jacobian rows attached and the carried
`p₀`-loaded residue live.  The named next unused row was the
`g₁`-cancelled head of `q₁`.

This file consumes that head.  After the carried substitutions
`t₂(a) = 6 g₁(a) t₁(a)` and `243 p₁(a) = g₁(a) u(a)`, the ninth solved
block evaluates to `36 g₁(a)` times the named head, so
`45349632 q₁(a) = g₁(a) · alignedNonsquareDegreeOneRootHead610(a)` at
every root of `H` simultaneously (an `H`-divisibility of the difference,
never a finite-root case split).  Pairing with the inhomogeneous Keller
row then factors `j` through `g₁(a)`.  Pairing the same head with the
degree-`1` Jacobian and eliminating `p₀'` on the residue-regular limb
does **not** force `j = 0`: CAS gives

`j = Φ(a) · V(a) / D(a)`

with derivative factor
`Φ = H'(2 t₁ t₃ - v) + g₁ (6 t₁ t₁' - u')`
and `V` an irreducible weighted-degree-`12` value form in
`(t₁ t₃ - v, u - 3 t₁², g₁, t₃, κ, κ₅, κ₇)`, coprime to `D`.  The
degree-`2` Jacobian is a multiple of the residue at a root, so it is
not an independent constraint on this chamber.

The complementary limb therefore resists.  No `False` is claimed, and
`PlaneKeller610AlignedNonsquareExclusion` is not discharged.  The next
unused datum is `alignedNonsquareDegreeOnePhi610`.  No total-degree or
twice-prime theorem is used.  No `sorry`, no new axioms, no finite-root
shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 1000000

/-! ## Derivative factor of the jac1–Keller elimination -/

/-- Derivative factor of the degree-`1` Jacobian paired with the Keller
row on the residue-regular complementary limb.  After the residue solves
`p₀` (linear coefficient `5(t₁ t₃ - v) - 2 κ t₃` nonzero at the root),
CAS yields `j = Φ(a) · V(a) / D(a)` with `V` irreducible of weighted
degree `12` and coprime to `D`.  Vanishing of `Φ` at both simple roots
is the next unused constraint. -/
def alignedNonsquareDegreeOnePhi610 {K : Type*} [CommRing K]
    (H g1 t1 u t3 v : K[X]) : K[X] :=
  H.derivative * ((2 : K[X]) * t1 * t3 - v) +
    g1 * ((6 : K[X]) * t1 * t1.derivative - u.derivative)

/-! ## Head identity at a root of `H` -/

variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 16000000 in
/-- At a root of `H`, the ninth solved block is `36 g₁` times the named
head after the carried substitutions `t₂ = 6 g₁ t₁` and
`243 p₁ = g₁ u`.  This is the evaluation form of the `H`-divisibility
`ninthBlock - 36 g₁ · head = H · (⋯)`, so it holds at both simple roots
at once. -/
theorem alignedNonsquare_ninthBlock_head_atRoot_610
    (H g1 t1 t2 u t3 a0 a1 : K[X]) (κ κ₃ κ₅ κ₇ : K)
    (x : K) (hx : H.eval x = 0)
    (ht2 : t2.eval x = (6 : K) * g1.eval x * t1.eval x)
    (ha1 : (243 : K) * a1.eval x = g1.eval x * u.eval x) :
    (alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 a0 a1
        κ κ₃ κ₅ κ₇).eval x =
      (36 : K) * g1.eval x *
        (alignedNonsquareDegreeOneRootHead610 a0 t1 u κ κ₃ κ₅ κ₇).eval x := by
  have h243 : (243 : K) ≠ 0 := by norm_num
  have ha1' : a1.eval x = (g1.eval x * u.eval x) / (243 : K) := by
    rw [eq_div_iff h243, mul_comm]
    exact ha1
  simp only [alignedNinthNonsquareSolved610,
    alignedNonsquareDegreeOneRootHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat]
  rw [hx, ht2, ha1']
  field_simp [h243]
  ring

set_option maxHeartbeats 8000000 in
/-- Clearing the ninth-block constant `1632586752 = 36 · 45349632` turns
the head identity into the named CAS relation on `q₁`. -/
theorem alignedNonsquare_q1_head_atRoot_610
    (H g1 t1 t2 u t3 a0 a1 b1 : K[X]) (κ κ₃ κ₅ κ₇ : K)
    (hq1 : (1632586752 : K[X]) * b1 =
      alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 a0 a1 κ κ₃ κ₅ κ₇)
    (x : K) (hx : H.eval x = 0)
    (ht2 : t2.eval x = (6 : K) * g1.eval x * t1.eval x)
    (ha1 : (243 : K) * a1.eval x = g1.eval x * u.eval x) :
    (45349632 : K) * b1.eval x =
      g1.eval x *
        (alignedNonsquareDegreeOneRootHead610 a0 t1 u κ κ₃ κ₅ κ₇).eval x := by
  have hblock :=
    alignedNonsquare_ninthBlock_head_atRoot_610 H g1 t1 t2 u t3 a0 a1
      κ κ₃ κ₅ κ₇ x hx ht2 ha1
  have hev := congrArg (fun w : K[X] => w.eval x) hq1
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat] at hev
  have hconst : (1632586752 : K) = (36 : K) * (45349632 : K) := by
    norm_num
  have h36 : (36 : K) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h36
  calc
    (36 : K) * ((45349632 : K) * b1.eval x)
        = (1632586752 : K) * b1.eval x := by
          rw [hconst, mul_assoc]
    _ = (alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 a0 a1
            κ κ₃ κ₅ κ₇).eval x := hev
    _ = (36 : K) * g1.eval x *
          (alignedNonsquareDegreeOneRootHead610 a0 t1 u κ κ₃ κ₅ κ₇).eval x :=
        hblock
    _ = (36 : K) * (g1.eval x *
          (alignedNonsquareDegreeOneRootHead610 a0 t1 u κ κ₃ κ₅ κ₇).eval x) := by
        ac_rfl

set_option maxHeartbeats 8000000 in
/-- Keller pairing of the head at a root of `H`: the original constant
factors as `j = g₁(a) · λ(a)` with
`λ = a₀' head / 45349632 - u q₀' / 243`.  On the complementary limb
`g₁(a) ≠ 0` this does not force `j = 0`. -/
theorem alignedNonsquare_keller_head_factor_atRoot_610
    (H g1 t1 t2 u t3 a0 a1 b1 b0 : K[X]) (κ κ₃ κ₅ κ₇ j : K)
    (hq1 : (1632586752 : K[X]) * b1 =
      alignedNinthNonsquareSolved610 H g1 t1 t2 u t3 a0 a1 κ κ₃ κ₅ κ₇)
    (hrow : a0.derivative * b1 - a1 * b0.derivative = Polynomial.C j)
    (x : K) (hx : H.eval x = 0)
    (ht2 : t2.eval x = (6 : K) * g1.eval x * t1.eval x)
    (ha1 : (243 : K) * a1.eval x = g1.eval x * u.eval x) :
    j = g1.eval x *
      ((a0.derivative.eval x *
          (alignedNonsquareDegreeOneRootHead610 a0 t1 u κ κ₃ κ₅ κ₇).eval x) *
          (45349632 : K)⁻¹ -
        (u.eval x * b0.derivative.eval x) * (243 : K)⁻¹) := by
  have hq1x :=
    alignedNonsquare_q1_head_atRoot_610 H g1 t1 t2 u t3 a0 a1 b1
      κ κ₃ κ₅ κ₇ hq1 x hx ht2 ha1
  have h243 : (243 : K) ≠ 0 := by norm_num
  have hC : (45349632 : K) ≠ 0 := by norm_num
  have hev := congrArg (fun w : K[X] => w.eval x) hrow
  simp only [Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C] at hev
  have hb1 : b1.eval x =
      (g1.eval x *
        (alignedNonsquareDegreeOneRootHead610 a0 t1 u κ κ₃ κ₅ κ₇).eval x) /
          (45349632 : K) := by
    rw [eq_div_iff hC, mul_comm (b1.eval x)]
    exact hq1x
  have ha1' : a1.eval x = (g1.eval x * u.eval x) / (243 : K) := by
    rw [eq_div_iff h243, mul_comm]
    exact ha1
  rw [hb1, ha1'] at hev
  field_simp [hC, h243] at hev ⊢
  linear_combination hev.symm

/-! ## Source-facing head and residual -/

variable [IsAlgClosed K]

set_option maxHeartbeats 16000000 in
/-- Source-facing head identity: at every root of the quadratic core the
solved `q₁` is `g₁` times the named head over `45349632`. -/
theorem normalized610ScaleTwo_alignedNonsquare_q1_head_atRoot
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (κ κ₃ κ₅ κ₇ : K) (g1 t1 u : K[X]),
      ∀ x : K, H.eval x = 0 →
        (45349632 : K) * (q.coeff 1).eval x =
          g1.eval x *
            (alignedNonsquareDegreeOneRootHead610 (p.coeff 0) t1 u
              κ κ₃ κ₅ κ₇).eval x := by
  dsimp only at haligned ⊢
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨κ, κ₃, κ₅, κ₇, _κ₉, g1, _f, t1, t2, u, t3, v, _hM, _hp5, _hf,
    _ht1, _ht2, _hu, ht3, hv, _hq0, hq1, _hq2, _hD0, _hE, _hF0, _hG,
    _hI0, _hJ, _hL0, _hO, _hΛ0, _hres⟩ :=
    normalized610ScaleTwo_alignedEleventhFace_nonsquareChamber_packet
      hsource hnsq haligned
  refine ⟨κ, κ₃, κ₅, κ₇, g1, t1, u, ?_⟩
  intro x hx
  have ht2x : t2.eval x = (6 : K) * g1.eval x * t1.eval x := by
    have hev := congrArg (fun w : K[X] => w.eval x) ht3
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_ofNat] at hev
    rw [hx] at hev
    linear_combination hev
  have ha1x : (243 : K) * (p.coeff 1).eval x = g1.eval x * u.eval x := by
    have hev := congrArg (fun w : K[X] => w.eval x) hv
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_ofNat] at hev
    rw [hx] at hev
    linear_combination hev
  exact alignedNonsquare_q1_head_atRoot_610 H g1 t1 t2 u t3 (p.coeff 0)
    (p.coeff 1) (q.coeff 1) κ κ₃ κ₅ κ₇ hq1 x hx ht2x ha1x

set_option maxHeartbeats 16000000 in
/-- Residual of the complementary `g₁(a) ≠ 0` limb after consuming the
named degree-`1` head against the Keller row.  The head identity holds
at both simple roots, `j` factors through `g₁(a)`, and the next unused
datum is the derivative factor `alignedNonsquareDegreeOnePhi610`.  The
limb is not closed: no `False` is claimed. -/
theorem normalized610ScaleTwo_alignedNonsquare_headResidual
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
          (∀ x : K, H.eval x = 0 → g1.eval x ≠ 0) ∧
            ∀ x : K, H.eval x = 0 →
              (45349632 : K) * (q.coeff 1).eval x =
                g1.eval x *
                  (alignedNonsquareDegreeOneRootHead610 (p.coeff 0) t1 u
                    κ κ₃ κ₅ κ₇).eval x) ∧
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
      ht1, ht2, hu, ht3, hv, hres, ?g1ne, ?head⟩
    · intro x hx hgx
      exact normalized610ScaleTwo_alignedNonsquare_g1Root_false
        hsource hnsq haligned x hx
        ⟨κ, κ₃, κ₅, κ₇, κ₉, f, t1, t2, u, t3, v, hp5, hgx, hq1, ht3, hv⟩
    · intro x hx
      have ht2x : t2.eval x = (6 : K) * g1.eval x * t1.eval x := by
        have hev := congrArg (fun w : K[X] => w.eval x) ht3
        simp only [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_ofNat] at hev
        rw [hx] at hev
        linear_combination hev
      have ha1x : (243 : K) * (p.coeff 1).eval x =
          g1.eval x * u.eval x := by
        have hev := congrArg (fun w : K[X] => w.eval x) hv
        simp only [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_ofNat] at hev
        rw [hx] at hev
        linear_combination hev
      exact alignedNonsquare_q1_head_atRoot_610 H g1 t1 t2 u t3
        (p.coeff 0) (p.coeff 1) (q.coeff 1) κ κ₃ κ₅ κ₇ hq1 x hx ht2x
        ha1x
  · exact (normalized610ScaleTwo_alignedNonsquare_residualPacket
      hsource hnsq haligned).2

#print axioms alignedNonsquare_ninthBlock_head_atRoot_610
#print axioms alignedNonsquare_q1_head_atRoot_610
#print axioms alignedNonsquare_keller_head_factor_atRoot_610
#print axioms normalized610ScaleTwo_alignedNonsquare_q1_head_atRoot
#print axioms normalized610ScaleTwo_alignedNonsquare_headResidual

end Max11DegreeRoutes
