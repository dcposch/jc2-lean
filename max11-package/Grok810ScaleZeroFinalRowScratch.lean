import Grok810DegreeZeroPrimitiveScratch

/-! # Scale-zero final Jacobian row for the normalized `(8,10)`, `H = 0` leaf

Continuation of `Fable810ScaleZeroFourteenthDefectScratch` on the constant
core `H = (C t)²`.  The tracked defect chain already forces the
discriminator `N` and every cleared defect through the weight-one-hundred-five
tail to ground constants on both constant faces of `N`.  The degree-`1`
row is the already-landed `piResidual810` integral.  This file consumes
the last unused Keller coefficient, the inhomogeneous degree-`0` Jacobian
row

```
(p₀)' q₁ - p₁ (q₀)' = j
```

of the same monic depression.  After the octic change that kills `z⁷`,
that row is `W G' - F X' = j / t`.  Unlike every higher row it equals
the nonzero Keller constant, so it is not a first integral and it
clears no further defect.  Its companion is the already-landed
grouped primitive `ρ`: on a monic octic/decic bracket the primitive
differentiates to the same constant `j / t`.  At this scale `h = C t`
is a nonzero scalar, so both identities are polynomial-degree
bookkeeping in `k[X]` — a nonzero constant Wronskian, and a primitive
whose derivative is the nonzero constant `j / t`.

A constant core has no finite root and no pole, so the scale-two
`h`-adic jet is unavailable.  CAS on the grouped primitive
(`derive_810_scale_zero_final_row.py`, outer degrees `(8,10)`, leading
powers `h⁴` and `h⁵` with `h` constant) identifies unique Newton faces
of degree greater than one.  One exact chamber is excluded: if both
`p₀` and `q₀` are constants then the last row collapses to `0 = j`.
The remaining Newton cones of the primitive are recorded as one named
residual on each constant face of `N`.

The Jacobian coefficient tower is fully consumed: there is no unused
row below degree `0`.  The packet does not close the leaf.  No
total-degree or twice-prime theorem is used.  No finite-root shortcut
is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section ScaleZeroFinalRow810

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal last Keller coefficient -/

/-- Generic degree-`0` identity of a differential Jacobian: the last
coefficient is the Wronskian `W dG - F dX`. -/
theorem differentialJacobian_coeff_0_810
    {F : Type*} [Field F] [Algebra k F]
    (d : Derivation k F F) (f g : F[X]) :
    (differentialJacobian d f g).coeff 0 =
      g.coeff 1 * d (f.coeff 0) - f.coeff 1 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal 0 :
      Finset (ℕ × ℕ)) = ({(0, 0)} : Finset (ℕ × ℕ)) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 0 =
        g.coeff 1 * d (f.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti, Finset.sum_singleton,
      coeff_coefficientDeriv, Polynomial.coeff_derivative]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 0 =
        f.coeff 1 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti, Finset.sum_singleton,
      coeff_coefficientDeriv, Polynomial.coeff_derivative]
    ring
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]

/-- Source-facing degree-`0` Jacobian row of a normalized scale-zero
`(8,10)` pair.  The Keller constant is nonzero. -/
theorem normalized810ScaleZero_degreeZeroRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ j : k, j ≠ 0 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j :=
  normalized810_degreeZeroJacobianRow hsource

/-- At scale zero the common core is constant; the degree-`0` row has no
`p₈'` or `q₁₀'` term, so it collapses to the same literal row. -/
theorem scaleZero_degreeZeroJacobianRow_810
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (_hHdegree : H.natDegree = 0)
    (_hp8 : p.coeff 8 = H ^ 4) (_hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 0).derivative * q.coeff 1 -
      p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j :=
  degreeZeroCoefficientJacobianRow_810 hp hq hjac

/-- Source-facing scale-zero collapse of the degree-`0` row. -/
theorem normalized810ScaleZero_degreeZeroRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ j : k, j ≠ 0 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j :=
  normalized810ScaleZero_degreeZeroRow hsource

/-- The last source row is a ground-field constant, and that constant is
the nonzero Keller parameter. -/
theorem normalized810ScaleZero_finalRow_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ j : k, j ≠ 0 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j :=
  normalized810ScaleZero_degreeZeroRow hsource

/-- Newton degree of the last Keller coefficient at scale zero: the
source Wronskian is a nonzero constant polynomial. -/
theorem normalized810ScaleZero_finalRow_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    ((p.coeff 0).derivative * q.coeff 1 -
      p.coeff 1 * (q.coeff 0).derivative).natDegree ≤ 0 := by
  dsimp only
  obtain ⟨j, _hj, hrow⟩ :=
    normalized810ScaleZero_finalRow_exists_C hsource
  rw [hrow]
  exact (natDegree_C j).le

/-- The two cross-products on the last row are unequal as polynomials:
`p₀' q₁ ≠ p₁ q₀'`.  This is the scale-zero form of the scale-two
boundary separation, now global rather than evaluated at a root. -/
theorem normalized810ScaleZero_finalRow_crossProducts_ne
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 0).derivative * q.coeff 1 ≠
      p.coeff 1 * (q.coeff 0).derivative := by
  dsimp only
  obtain ⟨j, hj, hrow⟩ :=
    normalized810ScaleZero_finalRow_exists_C hsource
  intro heq
  apply hj
  have : Polynomial.C j = (0 : k[X]) := by
    rw [← hrow, heq, sub_self]
  exact Polynomial.C_eq_zero.mp this

/-- Constant-lowest-coefficient chamber: if both `p₀` and `q₀` are
ground constants then the last row collapses to `0 = j`. -/
theorem normalized810ScaleZero_false_of_constant_p0_q0
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hp0 :
      (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0).natDegree =
        0)
    (hq0 :
      (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0).natDegree =
        0) :
    False := by
  obtain ⟨j, hj, hrow⟩ :=
    normalized810ScaleZero_finalRow_exists_C hsource
  obtain ⟨c0, hc0⟩ := natDegree_eq_zero.mp hp0
  obtain ⟨d0, hd0⟩ := natDegree_eq_zero.mp hq0
  have hp0der :
      (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0).derivative =
        0 := by
    rw [← hc0, derivative_C]
  have hq0der :
      (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0).derivative =
        0 := by
    rw [← hd0, derivative_C]
  have : Polynomial.C j = (0 : k[X]) := by
    rw [← hrow, hp0der, hq0der, zero_mul, mul_zero, sub_zero]
  exact hj (Polynomial.C_eq_zero.mp this)

/-! ## Depressed last row and the grouped primitive `ρ` -/

/-- After the constant-scale monic depression the last row is the
nonzero constant `j / t`.  No finite root is used. -/
theorem scaleZero_normalizedDegreeZeroRow_810
    {p q : k[X][X]} {j t : k}
    (ht : t ≠ 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    let hRF : RatFunc k := RatFunc.C t
    let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
    let f : (RatFunc k)[X] :=
      affineDepress68 hRF (octicDepressionR810 hRF a7)
        (sourceToRatFunc68 p)
    let g : (RatFunc k)[X] :=
      affineDepress68 hRF (octicDepressionR810 hRF a7)
        (sourceToRatFunc68 q)
    g.coeff 1 * ratFuncDerivation68 (f.coeff 0) -
      f.coeff 1 * ratFuncDerivation68 (g.coeff 0) =
        RatFunc.C (j / t) := by
  dsimp only
  let hRF : RatFunc k := RatFunc.C t
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  have hh : hRF ≠ 0 := by
    intro hzero
    apply ht
    apply RatFunc.C_injective
    simpa only [hRF, map_zero] using hzero
  have hbracket :=
    differentialJacobian_affineDepress_sourceToRatFunc68 p q j hRF
      (octicDepressionR810 hRF a7) hh hD
  have hcoeff :=
    congrArg (fun r : (RatFunc k)[X] => r.coeff 0) hbracket
  have hrow :
      (affineDepress68 hRF (octicDepressionR810 hRF a7)
            (sourceToRatFunc68 q)).coeff 1 *
          ratFuncDerivation68
            ((affineDepress68 hRF (octicDepressionR810 hRF a7)
              (sourceToRatFunc68 p)).coeff 0) -
        (affineDepress68 hRF (octicDepressionR810 hRF a7)
          (sourceToRatFunc68 p)).coeff 1 *
          ratFuncDerivation68
            ((affineDepress68 hRF (octicDepressionR810 hRF a7)
              (sourceToRatFunc68 q)).coeff 0) =
        RatFunc.C j / hRF := by
    have hzero := (differentialJacobian_coeff_0_810 ratFuncDerivation68
      (affineDepress68 hRF (octicDepressionR810 hRF a7)
        (sourceToRatFunc68 p))
      (affineDepress68 hRF (octicDepressionR810 hRF a7)
        (sourceToRatFunc68 q))).symm.trans hcoeff
    simpa [Polynomial.coeff_C] using hzero
  have hdiv : RatFunc.C j / hRF = RatFunc.C (j / t) := by
    simp only [hRF, map_div₀]
  exact hrow.trans hdiv

set_option maxHeartbeats 16000000 in
/-- On the same supplied constant-scale source, the grouped primitive
`ρ` differentiates to the nonzero constant `j / t`.  This is the
`(4,10)` ground-integration identity at the last row, not a first
integral. -/
theorem scaleZero_rhoResidual_deriv_eq_C_810
    {p q : k[X][X]} {j t lambda : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * (Polynomial.C t) ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    let hRF : RatFunc k := RatFunc.C t
    let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
    let f : (RatFunc k)[X] :=
      affineDepress68 hRF (octicDepressionR810 hRF a7)
        (sourceToRatFunc68 p)
    let g : (RatFunc k)[X] :=
      affineDepress68 hRF (octicDepressionR810 hRF a7)
        (sourceToRatFunc68 q)
    ratFuncDerivation68
        (rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 2) (g.coeff 1)) =
      RatFunc.C (j / t) := by
  dsimp only
  let hRF : RatFunc k := RatFunc.C t
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (octicDepressionR810 hRF a7)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (octicDepressionR810 hRF a7)
      (sourceToRatFunc68 q)
  have hh : hRF ≠ 0 := by
    intro hzero
    apply ht
    apply RatFunc.C_injective
    simpa only [hRF, map_zero] using hzero
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 8) = hRF ^ 8 := by
    simp only [hp8, hH, hRF, map_pow, RatFunc.algebraMap_C]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow, RatFunc.algebraMap_C]
    ring
  have hpDep := affineDepress_sourceOctic68 p hRF
    (octicDepressionR810 hRF a7) hp hh hpTop
  have hNrat :
      5 * a7 * hRF ^ 2 - 4 * b9 = RatFunc.C lambda * hRF ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    simpa only [hH, hRF, a7, b9, map_sub, map_mul, map_pow, map_ofNat,
      RatFunc.algebraMap_C] using hmapped
  have hLval :
      depressedL810 hRF (octicDepressionR810 hRF a7) b9 =
        RatFunc.C (-lambda / 4) := by
    have hL := depressedL810_eq_of_ninthPower hRF a7 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (octicDepressionR810 hRF a7) hh hD
  have hL0 : depressedL68 hRF (octicDepressionR810 hRF a7) a7 = 0 :=
    depressedL68_eq_zero_of_octicCenter hRF a7 hh
  have hf7 : f.coeff 7 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_seven, hL0]
  have hf8 : f.coeff 8 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_eight]
  have hf_high : ∀ n, 8 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_of_gt_eight _ _ _ _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n →
      (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, _hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (octicDepressionR810 hRF a7) hh hgTop hg_high_src
  have hg9L : g.coeff 9 =
      depressedL810 hRF (octicDepressionR810 hRF a7) b9 := by
    dsimp only [g]
    rw [hg9]
    simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46, b9]
  have hg9const : g.coeff 9 = RatFunc.C (-lambda / 4) := by
    rw [hg9L, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9const]
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 4) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hprim :
      ratFuncDerivation68
          (rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
            (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
            (g.coeff 3) (g.coeff 2) (g.coeff 1)) =
        RatFunc.C j / hRF := by
    have hconst :=
      rhoResidual810_deriv_eq_constant_of_monic_differentialJacobian
        ratFuncDerivation68 f g (RatFunc.C j / hRF)
        hf_high hf8 hf7 hg_high hg10 hLconst
        (by simpa only [f, g] using hbracket)
    simpa using hconst
  have hdiv : RatFunc.C j / hRF = RatFunc.C (j / t) := by
    simp only [hRF, map_div₀]
  exact hprim.trans hdiv

variable [IsAlgClosed k]

/-- Source-facing last-row packet: the Keller constant is nonzero, the
source Wronskian equals that constant, the weight-`105` defect remains
a ground constant, and after the constant-scale monic depression the
grouped primitive `ρ` differentiates to `j / t`. -/
theorem normalized810ScaleZero_exists_degreeZeroPrimitive
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda eta : k),
      t ≠ 0 ∧
      j ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      localClearedFifteenthDefect810 (Polynomial.C t)
          (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) lambda =
        Polynomial.C eta ∧
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      let hRF : RatFunc k := RatFunc.C t
      let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
      let f : (RatFunc k)[X] :=
        affineDepress68 hRF (octicDepressionR810 hRF a7)
          (sourceToRatFunc68 p)
      let g : (RatFunc k)[X] :=
        affineDepress68 hRF (octicDepressionR810 hRF a7)
          (sourceToRatFunc68 q)
      ratFuncDerivation68
          (rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
            (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
            (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
            (g.coeff 3) (g.coeff 2) (g.coeff 1)) =
        RatFunc.C (j / t) := by
  dsimp only
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  obtain ⟨t, ht, hHsq⟩ :=
    scaleZero_exists_constantSquareRoot_810 hH hHdegree
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  have hrow :
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j :=
    degreeZeroCoefficientJacobianRow_810 hp hq hjac
  obtain ⟨lambda, eta0, hN, hX⟩ :=
    scaleZero_fourteenthClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
  have hXconst :
      localClearedFifteenthDefect810 (Polynomial.C t)
          (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) lambda =
        Polynomial.C (eta0 * t ^ 105) := by
    rw [hX, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta0 (t ^ 105)).symm
  have hprim :=
    scaleZero_rhoResidual_deriv_eq_C_810 hp hq ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
      (by simpa only [p, q] using hN) hD
  refine ⟨t, j, lambda, eta0 * t ^ 105, ht, hj, hHsq,
    by simpa only [p, q] using hrow,
    by simpa only [p, q] using hXconst,
    by simpa only [p, q] using hN, ?_⟩
  simpa only [p, q] using hprim

/-- Exhausted constant-core packet: every Jacobian coefficient through
degree `0` is consumed, the defect tower remains a list of ground
constants, and the grouped primitive differentiates to the nonzero
constant `j / t`.  The leaf is not closed. -/
theorem normalized810ScaleZero_exhaustedPacket
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda eta : k),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      localClearedFifteenthDefect810 (Polynomial.C t)
          (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) lambda =
        Polynomial.C eta := by
  obtain ⟨t, j, lambda, eta, ht, hj, hHsq, hrow, hX, _hN, _hprim⟩ :=
    normalized810ScaleZero_exists_degreeZeroPrimitive hsource
  exact ⟨t, j, lambda, eta, ht, hj, div_ne_zero hj ht, hHsq, hrow, hX⟩

/-- Aligned discriminator branch: `λ = 0` still has a nonzero last row. -/
theorem normalized810ScaleZero_degreeZeroRow_of_aligned
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (haligned :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t j eta : k),
      t ≠ 0 ∧
      j ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      localClearedFifteenthDefect810 (Polynomial.C t)
          (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) 0 =
        Polynomial.C eta := by
  obtain ⟨j, hj, hrow⟩ :=
    normalized810ScaleZero_finalRow_exists_C hsource
  obtain ⟨t, eta, ht, hHsq, hX⟩ :=
    normalized810ScaleZero_aligned_exists_fourteenthClearedDefect hsource
      haligned
  refine ⟨t, j, eta * t ^ 105, ht, hj, hHsq, hrow, ?_⟩
  have hconst :
      localClearedFifteenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          0 =
        Polynomial.C (eta * t ^ 105) := by
    rw [hX, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta (t ^ 105)).symm
  exact hconst

/-- Nonzero discriminator branch: `λ ≠ 0` and the last row is still the
nonzero Keller constant. -/
theorem normalized810ScaleZero_degreeZeroRow_of_nonzero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t j lambda eta : k),
      t ≠ 0 ∧
      j ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7) *
            H -
        (4 : k[X]) *
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9) =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      localClearedFifteenthDefect810 (Polynomial.C t)
          (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) lambda =
        Polynomial.C eta := by
  obtain ⟨j, hj, hrow⟩ :=
    normalized810ScaleZero_finalRow_exists_C hsource
  obtain ⟨t, lambda, eta, ht, hlambda, hHsq, hN, hX⟩ :=
    normalized810ScaleZero_nonzero_exists_fourteenthClearedDefect hsource
      hnonzero
  refine ⟨t, j, lambda, eta * t ^ 105, ht, hj, hlambda, hHsq, hN, hrow, ?_⟩
  have hconst :
      localClearedFifteenthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          lambda =
        Polynomial.C (eta * t ^ 105) := by
    rw [hX, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta (t ^ 105)).symm
  exact hconst

/-! ## Named residuals of the two constant faces -/

/-- Aligned-face residual after the degree-`0` row: `λ = 0`, the last
row is the nonzero Keller constant, the weight-`105` defect is a ground
constant, and `ρ` differentiates to `j / t`.  CAS unique-face comparison
of the grouped primitive against derivative `C (j / t)` remains: the
aligned unique-`A` cancellation `385 B + 51 β = 0`, mixed-degree cones,
and unique-`B`/`D₀`/`E₀`/`F₀`/`G₀` chambers with vanishing combined
leading coefficient. -/
def Normalized810ScaleZeroAlignedFinalResidual
    {P Q : MvPolynomial (Fin 2) k} (H : k[X]) : Prop :=
  ∃ (t j eta : k),
    t ≠ 0 ∧
    j ≠ 0 ∧
    j / t ≠ 0 ∧
    H = (Polynomial.C t) ^ 2 ∧
    (5 : k[X]) *
        ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
          H -
      (4 : k[X]) *
        ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
      0 ∧
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 0).derivative * q.coeff 1 -
      p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
    localClearedFifteenthDefect810 (Polynomial.C t)
        (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
        (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
        (q.coeff 1) 0 =
      Polynomial.C eta ∧
    let hRF : RatFunc k := RatFunc.C t
    let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
    let f : (RatFunc k)[X] :=
      affineDepress68 hRF (octicDepressionR810 hRF a7)
        (sourceToRatFunc68 p)
    let g : (RatFunc k)[X] :=
      affineDepress68 hRF (octicDepressionR810 hRF a7)
        (sourceToRatFunc68 q)
    ratFuncDerivation68
        (rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 2) (g.coeff 1)) =
      RatFunc.C (j / t)

/-- Nonzero-face residual after the degree-`0` row: `λ ≠ 0`, the last
row is the nonzero Keller constant, the weight-`105` defect is a ground
constant, and `ρ` differentiates to `j / t`.  CAS unique-face comparison
of the grouped primitive against derivative `C (j / t)` remains: mixed
degree cones and unique-`B`/`D₀`/`E₀`/`F₀` chambers whose combined
leading coefficient vanishes.  The unique-`A` face `A⁸ L`, unique-`C₀`
face `C₀⁴ L`, and unique-`G₀` face `G₀² L` are the next unused
leading-coefficient data on this face. -/
def Normalized810ScaleZeroNonzeroFinalResidual
    {P Q : MvPolynomial (Fin 2) k} (H : k[X]) : Prop :=
  ∃ (t j lambda eta : k),
    t ≠ 0 ∧
    j ≠ 0 ∧
    j / t ≠ 0 ∧
    lambda ≠ 0 ∧
    H = (Polynomial.C t) ^ 2 ∧
    (5 : k[X]) *
        ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
          H -
      (4 : k[X]) *
        ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
      Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 0).derivative * q.coeff 1 -
      p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
    localClearedFifteenthDefect810 (Polynomial.C t)
        (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
        (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
        (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
        (q.coeff 1) lambda =
      Polynomial.C eta ∧
    let hRF : RatFunc k := RatFunc.C t
    let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
    let f : (RatFunc k)[X] :=
      affineDepress68 hRF (octicDepressionR810 hRF a7)
        (sourceToRatFunc68 p)
    let g : (RatFunc k)[X] :=
      affineDepress68 hRF (octicDepressionR810 hRF a7)
        (sourceToRatFunc68 q)
    ratFuncDerivation68
        (rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 2) (g.coeff 1)) =
      RatFunc.C (j / t)

theorem normalized810ScaleZero_aligned_finalResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (haligned :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    Normalized810ScaleZeroAlignedFinalResidual (P := P) (Q := Q) H := by
  obtain ⟨t, j, lambda, eta, ht, hj, hHsq, hrow, hX, hN, hprim⟩ :=
    normalized810ScaleZero_exists_degreeZeroPrimitive hsource
  have hlambda : lambda = 0 := by
    have hN0 :
        (5 : k[X]) *
            ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
              H -
          (4 : k[X]) *
            ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
          Polynomial.C lambda * (Polynomial.C t) ^ 9 := hN
    have : Polynomial.C lambda * (Polynomial.C t) ^ 9 = 0 :=
      hN0.symm.trans haligned
    have ht9 : (Polynomial.C t : k[X]) ^ 9 ≠ 0 :=
      pow_ne_zero 9 (Polynomial.C_ne_zero.mpr ht)
    have hC : Polynomial.C lambda = (0 : k[X]) :=
      (mul_eq_zero.mp this).resolve_right ht9
    exact Polynomial.C_eq_zero.mp hC
  refine ⟨t, j, eta, ht, hj, div_ne_zero hj ht, hHsq, haligned, hrow, ?_,
    ?_⟩
  · simpa [hlambda] using hX
  · simpa [hlambda] using hprim

theorem normalized810ScaleZero_nonzero_finalResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    Normalized810ScaleZeroNonzeroFinalResidual (P := P) (Q := Q) H := by
  obtain ⟨t, j, lambda, eta, ht, hj, hHsq, hrow, hX, hN, hprim⟩ :=
    normalized810ScaleZero_exists_degreeZeroPrimitive hsource
  have hlambda : lambda ≠ 0 := by
    intro h0
    apply hnonzero
    simpa [h0, map_zero, zero_mul] using hN
  exact ⟨t, j, lambda, eta, ht, hj, div_ne_zero hj ht, hlambda, hHsq, hN,
    hrow, hX, hprim⟩

/-- Glue of the two constant faces: the scale-zero source is empty once
each face residual is excluded.  This is the `(8,10)` form of
`planeKellerNormalized810LowScaleRoute_of_faceExclusions` at scale
zero.  Neither residual is claimed empty here. -/
theorem normalized810ScaleZero_impossible_of_faceResiduals
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (haligned :
      Normalized810ScaleZeroAlignedFinalResidual (P := P) (Q := Q) H →
        False)
    (hnonzero :
      Normalized810ScaleZeroNonzeroFinalResidual (P := P) (Q := Q) H →
        False) :
    False := by
  rcases normalized810ScaleZero_fourteenthClearedDefectFirstFace hsource with
    ⟨t, ht, hHsq, hfaces⟩
  rcases hfaces with hN0 | hNne
  · exact haligned
      (normalized810ScaleZero_aligned_finalResidual hsource hN0.1)
  · have hNne' :
        (5 : k[X]) *
            ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
              H -
          (4 : k[X]) *
            ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
          0 := by
      obtain ⟨lambda, eta, hlambda, hN, _hX⟩ := hNne
      intro h0
      apply hlambda
      have : Polynomial.C lambda * (Polynomial.C t) ^ 9 = 0 :=
        hN.symm.trans h0
      have ht9 : (Polynomial.C t : k[X]) ^ 9 ≠ 0 :=
        pow_ne_zero 9 (Polynomial.C_ne_zero.mpr ht)
      have hC : Polynomial.C lambda = (0 : k[X]) :=
        (mul_eq_zero.mp this).resolve_right ht9
      exact Polynomial.C_eq_zero.mp hC
    exact hnonzero
      (normalized810ScaleZero_nonzero_finalResidual hsource hNne')

/-- Honest residual of the fully consumed Jacobian tower.

The last row is the inhomogeneous identity `p₀' q₁ - p₁ q₀' = C j`
with `j ≠ 0`.  After the constant-scale monic depression that identity
is `G' W - F X' = j / t`, and the grouped primitive `ρ` differentiates
to the same nonzero constant.  Every cleared defect of the tower
remains a ground constant.  There is no unused Jacobian coefficient.

The leaf is not closed.  A constant core has no finite root, so the
scale-two square-chamber peel does not drop Newton degree.  The missing
input for `normalized810ScaleZero_impossible` is the `(4,10)`-style
polynomial-trajectory valuation exhaustion of the remaining free core
`(A, B, C₀, D₀, E₀, F₀, G₀)` against those constant defects together
with the inhomogeneous identity that `ρ` has derivative `C (j / t) ≠ 0`.
CAS unique-face data: on the nonzero face the next unused leading
coefficients are `A⁸ L`, `C₀⁴ L`, and `G₀² L`; on the aligned face
the next unused datum is the combined `A⁷` coefficient
`51 (385 B + 51 β)`. -/
theorem normalized810ScaleZero_finalRowResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    Normalized810ScaleZeroAlignedFinalResidual (P := P) (Q := Q) H ∨
      Normalized810ScaleZeroNonzeroFinalResidual (P := P) (Q := Q) H := by
  rcases normalized810ScaleZero_fourteenthClearedDefectFirstFace hsource with
    ⟨t, ht, hHsq, hfaces⟩
  rcases hfaces with hN0 | hNne
  · exact Or.inl
      (normalized810ScaleZero_aligned_finalResidual hsource hN0.1)
  · have hNne' :
        (5 : k[X]) *
            ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
              H -
          (4 : k[X]) *
            ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
          0 := by
      obtain ⟨lambda, eta, hlambda, hN, _hX⟩ := hNne
      intro h0
      apply hlambda
      have : Polynomial.C lambda * (Polynomial.C t) ^ 9 = 0 :=
        hN.symm.trans h0
      have ht9 : (Polynomial.C t : k[X]) ^ 9 ≠ 0 :=
        pow_ne_zero 9 (Polynomial.C_ne_zero.mpr ht)
      have hC : Polynomial.C lambda = (0 : k[X]) :=
        (mul_eq_zero.mp this).resolve_right ht9
      exact Polynomial.C_eq_zero.mp hC
    exact Or.inr
      (normalized810ScaleZero_nonzero_finalResidual hsource hNne')

end ScaleZeroFinalRow810

#print axioms differentialJacobian_coeff_0_810
#print axioms normalized810ScaleZero_degreeZeroRow
#print axioms scaleZero_degreeZeroJacobianRow_810
#print axioms normalized810ScaleZero_degreeZeroRow_collapsed
#print axioms normalized810ScaleZero_finalRow_exists_C
#print axioms normalized810ScaleZero_finalRow_natDegree_le_zero
#print axioms normalized810ScaleZero_finalRow_crossProducts_ne
#print axioms normalized810ScaleZero_false_of_constant_p0_q0
#print axioms scaleZero_normalizedDegreeZeroRow_810
#print axioms scaleZero_rhoResidual_deriv_eq_C_810
#print axioms normalized810ScaleZero_exists_degreeZeroPrimitive
#print axioms normalized810ScaleZero_exhaustedPacket
#print axioms normalized810ScaleZero_degreeZeroRow_of_aligned
#print axioms normalized810ScaleZero_degreeZeroRow_of_nonzero
#print axioms normalized810ScaleZero_aligned_finalResidual
#print axioms normalized810ScaleZero_nonzero_finalResidual
#print axioms normalized810ScaleZero_impossible_of_faceResiduals
#print axioms normalized810ScaleZero_finalRowResidual

end Max11DegreeRoutes
