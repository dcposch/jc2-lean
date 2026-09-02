import Grok610ScaleTwoAlignedNonsquareHeadScratch
import Grok610RemainingAlignedFacesScratch

/-! # Global argument on the aligned-nonsquare `(6,10)` chamber

Untracked working note.  No tracked file was edited.

Root-local rows are exhausted (`Grok610ScaleTwoAlignedNonsquareHeadScratch`):
at a simple root `a` of the quadratic core, `45349632 q₁(a) = g₁(a) head(a)`
and `j = Φ(a) V(a) / D(a)` with `Φ = alignedNonsquareDegreeOnePhi610` and `V`
an irreducible weighted-degree-`12` value form coprime to `D`.  The degree-`2`
Jacobian is a residue multiple, so it is not an independent constraint.

CAS jobs `610-aligned-nonsquare-global-lc` and
`610-aligned-nonsquare-descent` work over `k[X]` modulo
`H = X² + s X + t` (discriminant `s² - 4 t ≠ 0`), treating the Keller row
and the degree-`1` Jacobian as polynomial identities in `X` rather than
root evaluations.

* Constant witnesses (`g₁, t₁, u, t₃, v, p₀` of derivative zero): the
  tenth block is `C A + H · C B`, so `q₀' = H' · C B`.  With `p₀' = 0`
  the Keller row is `- p₁ q₀'`.  Either `B = 0` and `j = 0`, or the
  product has `X`-degree `3` (`v ≠ 0`) or `1` (`v = 0` and `p₁ ≠ 0`),
  contradicting `p₀' q₁ - p₁ q₀' = C j`.  This limb is **closed**.
* Linear witnesses: residue leading coefficient `-5120 t₁₁ t₃₁³`
  (monic `H`) forces `t₁₁ = 0` or `t₃₁ = 0`.  Both leftover limbs still
  have positive Keller degree after the first peel.
* Equal-degree principal symbol `d ≥ 3`: jac1 leading coefficient is
  proportional to `G₁² T₁⁶`; residue leading coefficient is
  `1280 T₃ (G₁² T₃² + 18 G₁ T₁² T₃ + 63 T₁⁴)`.  Vanishing drops at
  least one letter out of the top degree, but mixed-degree Newton
  strata remain.
* Type C (equal values at both roots): `j` constant gives
  `(2 d Δφ + g₁ (C₁ - C₂)) V = 0` with `d = H'(a₁) = -H'(a₂)` and
  `C = 6 t₁ t₁' - u'`.

The `(4,10)` nonsquare chamber closed by a transverse `g = 0` root
(`normalized410ScaleTwo_alignedNonsquare_false`); that limb is already
dead here.  The complementary positive-degree witnesses are **not**
closed.  No `PlaneKeller610AlignedNonsquareExclusion` is discharged.

The next unused datum is the mixed-degree leading-coefficient descent
of the Keller / degree-`1` Jacobian identities (equivalently the two-root
remainder of `Φ V - j D` after the linear obstruction).  No total-degree
or twice-prime theorem is used.  No `sorry`, no new axioms, no
finite-root shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000

/-- Inventory alias: the remaining aligned-nonsquare exclusion is not
discharged by this file. -/
def planeKeller610AlignedNonsquareExclusion_open
    {K : Type*} [Field K] : Prop :=
  PlaneKeller610AlignedNonsquareExclusion (K := K)

/-! ## Tenth-block split used by the constant-witness degree argument -/

/-- `H`-coefficient of `alignedTenthNonsquareSolved610`. -/
def alignedTenthNonsquareHCoef610 {K : Type*} [CommRing K]
    (g1 t1 u t3 v : K[X]) (κ : K) : K[X] :=
  (184320 : K[X]) * t1 ^ 2 * t3 ^ 2 - (184320 : K[X]) * t1 * t3 * v -
    (30720 : K[X]) * u * t3 ^ 2 + (10240 : K[X]) * t3 ^ 3 * g1 +
    (92160 : K[X]) * v ^ 2 -
    Polynomial.C κ * ((73728 : K[X]) * t1 * t3 ^ 2) +
    Polynomial.C κ * ((73728 : K[X]) * t3 * v)

/-- `H`-free summand of `alignedTenthNonsquareSolved610`. -/
def alignedTenthNonsquareHFree610 {K : Type*} [CommRing K]
    (g1 t1 u a0 : K[X]) (κ κ₃ κ₅ κ₇ : K) : K[X] :=
  (-((387072 : K[X]) * t1 ^ 5) + (368640 : K[X]) * t1 ^ 3 * u -
    (201553920 : K[X]) * t1 ^ 2 * a0 - (92160 : K[X]) * t1 * u ^ 2 +
    (134369280 : K[X]) * u * a0 - Polynomial.C κ₇ * ((72 : K[X]) * t1) +
    Polynomial.C κ₅ * ((1152 : K[X]) * t1 ^ 2) - Polynomial.C κ₅ * ((768 :
    K[X]) * u) - Polynomial.C κ₃ * ((20155392 : K[X]) * a0) + Polynomial.C
    κ * ((276480 : K[X]) * t1 ^ 4) - Polynomial.C κ * ((221184 : K[X]) *
    t1 ^ 2 * u) + Polynomial.C κ * ((161243136 : K[X]) * t1 * a0) +
    Polynomial.C κ * ((36864 : K[X]) * u ^ 2))

theorem alignedTenthNonsquareSolved_split_610 {K : Type*} [CommRing K]
    (H g1 t1 u t3 v a0 : K[X]) (κ κ₃ κ₅ κ₇ : K) :
    alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ =
      alignedTenthNonsquareHFree610 g1 t1 u a0 κ κ₃ κ₅ κ₇ +
        H * alignedTenthNonsquareHCoef610 g1 t1 u t3 v κ := by
  simp only [alignedTenthNonsquareSolved610,
    alignedTenthNonsquareHFree610, alignedTenthNonsquareHCoef610]

/-! ## Constant-witness degree lemmas -/

variable {K : Type*} [Field K] [CharZero K]

private lemma natDegree_le_zero_of_derivative_eq_zero
    {p : K[X]} (hp : p.derivative = 0) : p.natDegree ≤ 0 :=
  (derivative_eq_zero.mp hp).le

theorem alignedTenthNonsquareHCoef_derivative_of_constants_610
    (g1 t1 u t3 v : K[X]) (κ : K)
    (hg1 : g1.derivative = 0) (ht1 : t1.derivative = 0)
    (hu : u.derivative = 0) (ht3 : t3.derivative = 0)
    (hv : v.derivative = 0) :
    (alignedTenthNonsquareHCoef610 g1 t1 u t3 v κ).derivative = 0 := by
  have hg1le := natDegree_le_zero_of_derivative_eq_zero hg1
  have ht1le := natDegree_le_zero_of_derivative_eq_zero ht1
  have hule := natDegree_le_zero_of_derivative_eq_zero hu
  have ht3le := natDegree_le_zero_of_derivative_eq_zero ht3
  have hvle := natDegree_le_zero_of_derivative_eq_zero hv
  have hle : (alignedTenthNonsquareHCoef610 g1 t1 u t3 v κ).natDegree ≤ 0 := by
    simp only [alignedTenthNonsquareHCoef610]
    compute_degree
    omega
  exact derivative_eq_zero.mpr (Nat.eq_zero_of_le_zero hle)

set_option maxHeartbeats 8000000 in
theorem alignedTenthNonsquareHFree_derivative_of_constants_610
    (g1 t1 u a0 : K[X]) (κ κ₃ κ₅ κ₇ : K)
    (hg1 : g1.derivative = 0) (ht1 : t1.derivative = 0)
    (hu : u.derivative = 0) (ha0 : a0.derivative = 0) :
    (alignedTenthNonsquareHFree610 g1 t1 u a0 κ κ₃ κ₅ κ₇).derivative =
      0 := by
  have hg1le := natDegree_le_zero_of_derivative_eq_zero hg1
  have ht1le := natDegree_le_zero_of_derivative_eq_zero ht1
  have hule := natDegree_le_zero_of_derivative_eq_zero hu
  have ha0le := natDegree_le_zero_of_derivative_eq_zero ha0
  have hle :
      (alignedTenthNonsquareHFree610 g1 t1 u a0 κ κ₃ κ₅ κ₇).natDegree ≤ 0 := by
    simp only [alignedTenthNonsquareHFree610]
    compute_degree
    omega
  exact derivative_eq_zero.mpr (Nat.eq_zero_of_le_zero hle)

set_option maxHeartbeats 4000000 in
theorem alignedTenthNonsquareSolved_derivative_of_constants_610
    (H g1 t1 u t3 v a0 : K[X]) (κ κ₃ κ₅ κ₇ : K)
    (hg1 : g1.derivative = 0) (ht1 : t1.derivative = 0)
    (hu : u.derivative = 0) (ht3 : t3.derivative = 0)
    (hv : v.derivative = 0) (ha0 : a0.derivative = 0) :
    (alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇).derivative =
      H.derivative * alignedTenthNonsquareHCoef610 g1 t1 u t3 v κ := by
  rw [alignedTenthNonsquareSolved_split_610, derivative_add, derivative_mul,
    alignedTenthNonsquareHFree_derivative_of_constants_610 _ _ _ _ _ _ _ _
      hg1 ht1 hu ha0,
    alignedTenthNonsquareHCoef_derivative_of_constants_610 _ _ _ _ _ _
      hg1 ht1 hu ht3 hv]
  ring

theorem alignedNonsquare_H_mul_derivative_natDegree_610
    {H : K[X]} (hH : H ≠ 0) (hdeg : H.natDegree = 2) :
    (H * H.derivative).natDegree = 3 := by
  have hpos : 0 < H.natDegree := by
    rw [hdeg]
    norm_num
  have hdH : H.derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
  rw [natDegree_mul hH hdH, natDegree_derivative, hdeg]

set_option maxHeartbeats 16000000 in
/-- Constant witnesses make the inhomogeneous Keller row either `0` or of
positive `X`-degree, so it cannot equal `C j` with `j ≠ 0`. -/
theorem alignedNonsquare_constantWitness_false_610
    {H g1 t1 u t3 v a0 a1 b0 b1 : K[X]} {κ κ₃ κ₅ κ₇ κ₉ j : K}
    (hH : H ≠ 0) (hdeg : H.natDegree = 2)
    (hg1 : g1.derivative = 0) (ht1 : t1.derivative = 0)
    (hu : u.derivative = 0) (ht3 : t3.derivative = 0)
    (hv : v.derivative = 0) (ha0 : a0.derivative = 0)
    (hp1 : (243 : K[X]) * a1 - g1 * u = H * v)
    (hq0 : (9795520512 : K[X]) * b0 =
      alignedTenthNonsquareSolved610 H g1 t1 u t3 v a0 κ κ₃ κ₅ κ₇ -
        Polynomial.C κ₉)
    (hrow : a0.derivative * b1 - a1 * b0.derivative = Polynomial.C j)
    (hj : j ≠ 0) : False := by
  have hTderiv :=
    alignedTenthNonsquareSolved_derivative_of_constants_610 H g1 t1 u t3 v
      a0 κ κ₃ κ₅ κ₇ hg1 ht1 hu ht3 hv ha0
  have hb0deriv : (9795520512 : K[X]) * b0.derivative =
      H.derivative * alignedTenthNonsquareHCoef610 g1 t1 u t3 v κ := by
    have h := congrArg derivative hq0
    have hNder : derivative (9795520512 : K[X]) = 0 := by
      have hdegN : (9795520512 : K[X]).natDegree = 0 := by
        have hC : (9795520512 : K[X]) = Polynomial.C (9795520512 : K) :=
          (Polynomial.C_eq_natCast 9795520512).symm
        rw [hC, natDegree_C]
      exact derivative_eq_zero.mpr hdegN
    simp only [derivative_sub, derivative_mul, derivative_C, hNder,
      zero_mul, zero_add, sub_zero, hTderiv] at h
    exact h
  have hrow' : -a1 * b0.derivative = Polynomial.C j := by
    simpa [ha0, sub_eq_add_neg, zero_mul, zero_add, neg_mul] using hrow
  let B := alignedTenthNonsquareHCoef610 g1 t1 u t3 v κ
  have hcomb : -a1 * (H.derivative * B) =
      (9795520512 : K[X]) * Polynomial.C j := by
    have h :=
      congrArg (fun w : K[X] => (9795520512 : K[X]) * w) hrow'
    have hassoc : (9795520512 : K[X]) * (-a1 * b0.derivative) =
        -a1 * ((9795520512 : K[X]) * b0.derivative) := by
      ring
    rw [hassoc, hb0deriv] at h
    exact h
  have hprod : -a1 * (H.derivative * B) =
      Polynomial.C ((9795520512 : K) * j) := by
    have hN' : (9795520512 : K[X]) = Polynomial.C (9795520512 : K) :=
      Polynomial.C_eq_natCast 9795520512
    rw [hN', ← Polynomial.C_mul] at hcomb
    exact hcomb
  have hBder : B.derivative = 0 :=
    alignedTenthNonsquareHCoef_derivative_of_constants_610 g1 t1 u t3 v κ
      hg1 ht1 hu ht3 hv
  have ha1 : (243 : K[X]) * a1 = g1 * u + H * v := by
    linear_combination hp1
  by_cases hB0 : B = 0
  · have : Polynomial.C ((9795520512 : K) * j) = 0 := by
      rw [hB0, mul_zero, mul_zero] at hprod
      exact hprod.symm
    have hjN : (9795520512 : K) * j = 0 := Polynomial.C_eq_zero.mp this
    exact hj ((mul_eq_zero.mp hjN).resolve_left (by norm_num))
  · have hBdeg : B.natDegree = 0 := derivative_eq_zero.mp hBder
    have hvdeg : v.natDegree = 0 := derivative_eq_zero.mp hv
    have hg1deg : g1.natDegree = 0 := derivative_eq_zero.mp hg1
    have hudeg : u.natDegree = 0 := derivative_eq_zero.mp hu
    have hposH : 0 < H.natDegree := by
      rw [hdeg]
      norm_num
    have hdH : H.derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
    have hHddeg : H.derivative.natDegree = 1 := by
      rw [natDegree_derivative, hdeg]
    have hTH : (H.derivative * B).natDegree = 1 := by
      rw [natDegree_mul hdH hB0, hHddeg, hBdeg]
    have hCleared :
        -((g1 * u + H * v) * (H.derivative * B)) =
          Polynomial.C ((243 : K) * ((9795520512 : K) * j)) := by
      have h := congrArg (fun w : K[X] => (243 : K[X]) * w) hprod
      have hassoc : (243 : K[X]) * (-a1 * (H.derivative * B)) =
          -(((243 : K[X]) * a1) * (H.derivative * B)) := by
        ring
      have h243C : (243 : K[X]) = Polynomial.C (243 : K) :=
        Polynomial.C_eq_natCast 243
      rw [hassoc, ha1, h243C, ← Polynomial.C_mul] at h
      exact h
    by_cases hv0 : v = 0
    · have hgu : g1 * u + H * v = g1 * u := by simp [hv0]
      rw [hgu] at hCleared
      by_cases hgu0 : g1 * u = 0
      · have : Polynomial.C ((243 : K) * ((9795520512 : K) * j)) = 0 := by
          simpa [hgu0] using hCleared
        have hjN : (243 : K) * ((9795520512 : K) * j) = 0 :=
          Polynomial.C_eq_zero.mp this
        rcases mul_eq_zero.mp hjN with h | h
        · exact absurd h (by norm_num)
        · rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' (by norm_num)
          · exact hj h'
      · have hguNe : g1 * u ≠ 0 := hgu0
        have hguDeg : (g1 * u).natDegree = 0 := by
          have hg1ne : g1 ≠ 0 := fun hg10 => hgu0 (by simp [hg10])
          have hune : u ≠ 0 := fun hu0 => hgu0 (by simp [hu0])
          rw [natDegree_mul hg1ne hune, hg1deg, hudeg]
        have hLdeg : ((g1 * u) * (H.derivative * B)).natDegree = 1 := by
          rw [natDegree_mul hguNe (mul_ne_zero hdH hB0), hguDeg, hTH]
        have hneg :
            (-((g1 * u) * (H.derivative * B))).natDegree = 1 := by
          simpa [natDegree_neg] using hLdeg
        have hRdeg :
            (Polynomial.C ((243 : K) * ((9795520512 : K) * j))).natDegree =
              0 :=
          natDegree_C _
        rw [hCleared, hRdeg] at hneg
        exact (show ¬(0 : ℕ) = 1 from by decide) hneg
    · have hvNe : v ≠ 0 := hv0
      have hHv : (H * v).natDegree = 2 := by
        rw [natDegree_mul hH hvNe, hdeg, hvdeg]
      have hsum : (g1 * u + H * v).natDegree = 2 := by
        have hlt : (g1 * u).natDegree < (H * v).natDegree := by
          rw [hHv]
          by_cases hg10 : g1 = 0
          · simp [hg10]
          · by_cases hu0 : u = 0
            · simp [hu0]
            · have : (g1 * u).natDegree = 0 := by
                rw [natDegree_mul hg10 hu0, hg1deg, hudeg]
              omega
        rw [natDegree_add_eq_right_of_natDegree_lt hlt, hHv]
      have hsumNe : g1 * u + H * v ≠ 0 := by
        intro hz
        rw [hz, natDegree_zero] at hsum
        exact (show ¬(0 : ℕ) = 2 from by decide) hsum
      have hLdeg :
          ((g1 * u + H * v) * (H.derivative * B)).natDegree = 3 := by
        rw [natDegree_mul hsumNe (mul_ne_zero hdH hB0), hsum, hTH]
      have hneg :
          (-((g1 * u + H * v) * (H.derivative * B))).natDegree = 3 := by
        simpa [natDegree_neg] using hLdeg
      have hRdeg :
          (Polynomial.C ((243 : K) * ((9795520512 : K) * j))).natDegree =
            0 :=
        natDegree_C _
      rw [hCleared, hRdeg] at hneg
      exact (show ¬(0 : ℕ) = 3 from by decide) hneg

/-! ## Source-facing constant-witness kill -/

variable [IsAlgClosed K]

set_option maxHeartbeats 16000000 in
/-- Every nonsquare aligned scale-two `(6,10)` source with constant
carried witnesses `g₁, t₁, u, t₃, v, p₀` is impossible: the Keller row
cannot be the nonzero constant `j`. -/
theorem normalized610ScaleTwo_alignedNonsquare_constantWitness_false
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : K[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hconst :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      ∃ (κ κ₃ κ₅ κ₇ κ₉ : K) (g1 t1 u t3 v : K[X]),
        (243 : K[X]) * p.coeff 1 - g1 * u = H * v ∧
          (9795520512 : K[X]) * q.coeff 0 =
            alignedTenthNonsquareSolved610 H g1 t1 u t3 v (p.coeff 0)
                κ κ₃ κ₅ κ₇ - Polynomial.C κ₉ ∧
            g1.derivative = 0 ∧ t1.derivative = 0 ∧ u.derivative = 0 ∧
              t3.derivative = 0 ∧ v.derivative = 0 ∧
                (p.coeff 0).derivative = 0) :
    False := by
  dsimp only at haligned hconst
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  obtain ⟨κ, κ₃, κ₅, κ₇, κ₉, g1, t1, u, t3, v, hv, hq0, hg1d, ht1d, hud,
    ht3d, hvd, ha0d⟩ := hconst
  obtain ⟨j, hj, hrow⟩ :=
    normalized610ScaleTwo_alignedFinalKellerRow hsource haligned
  exact alignedNonsquare_constantWitness_false_610 hsource.1 hsource.2.1
    hg1d ht1d hud ht3d hvd ha0d hv hq0 hrow hj

/-- Residual of the aligned-nonsquare chamber after the global
constant-witness kill.  The carried residue, the degree-`1` head, and
`g₁(a) ≠ 0` at both simple roots remain; `j = Φ V / D` at a root does
not force `j = 0` on positive-degree witnesses.  The exclusion
`PlaneKeller610AlignedNonsquareExclusion` is not discharged.  The next
unused datum is the mixed-degree leading-coefficient descent of the
Keller identity (CAS: linear residue LC `-5120 t₁₁ t₃₁³`, equal-degree
`d ≥ 3` jac1 LC `∝ G₁² T₁⁶`). -/
theorem normalized610ScaleTwo_alignedNonsquare_globalResidual
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
              p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j) :=
  normalized610ScaleTwo_alignedNonsquare_headResidual hsource hnsq
    haligned

#print axioms alignedTenthNonsquareSolved_split_610
#print axioms alignedTenthNonsquareHCoef_derivative_of_constants_610
#print axioms alignedTenthNonsquareHFree_derivative_of_constants_610
#print axioms alignedTenthNonsquareSolved_derivative_of_constants_610
#print axioms alignedNonsquare_H_mul_derivative_natDegree_610
#print axioms alignedNonsquare_constantWitness_false_610
#print axioms normalized610ScaleTwo_alignedNonsquare_constantWitness_false
#print axioms normalized610ScaleTwo_alignedNonsquare_globalResidual

end Max11DegreeRoutes
