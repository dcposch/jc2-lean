import Fable610ScaleZeroTwelfthDefectSpeedTPart101Scratch

/-! # Scale-zero twelfth cleared defect for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Fable610ScaleZeroEleventhDefectScratch` on the constant
core `H = (C t)²`.  The eleventh packet already forces the discriminator
`N`, the weight-fifty-five defect `κ`, and the weight-sixty defect `λ`
to ground constants, including the exact selectors
`3134566563840 p₀ q₅ h⁵⁰` and `172186884 p₀ q₄ h⁵⁶`.  This file
consumes the next unused Keller coefficient, the degree-`2` Jacobian
row

```
(p₂)' (1 q₁) + (p₁)' (2 q₂) + (p₀)' (3 q₃)
  - (3 p₃) q₀' - (2 p₂) q₁' - (1 p₁) q₂' = 0
```

of the same monic depression.  After the sextic change that kills `z⁵`,
that row is `3 U E' + 2 V D' + W C' - D V' - 2 C W' - 3 B X' = 0`.
The derivative `X'` is eliminated through the degree-`5` row and `W'`
through the degree-`6` row.  Unlike the higher rows, the reduced
`1`-form of the degree-`2` row is not exact on its own: its exterior
derivative is `-3 dA ∧ dκ`, so the already-consumed degree-`4` row
re-enters with the polynomial coefficient `-(1/12) A`, and the first
integral `μ` obeys `d μ = (1/6)·row₂ - (1/12)·A·row₄`.  The `μ`
formula, its weight-sixty-five clearing by `12582912 h⁶⁵`, the solved
derivative forms, and the aligned `227`-monomial specialization were
derived and cross-checked independently (closedness of the corrected
`1`-form, the identity `d μ = (1/6) row₂ - (1/12) A row₄`, and a
rational end-to-end evaluation of the cleared `285`-monomial
polynomial).  The derivation-in-zero reduction keeps the sub-residuals
opaque so the tower hypotheses fire, and supplies the complete
constant-derivative kill set from `d (1/2) = 0` through
`d (77/15552) = 0` and `d (A⁶)`, `d (B⁴)`, `d (C³)`.

The degree-`5` iota first integral, the exact `18 q₀ h⁵⁰` residual, the
weight-fifty-five kappa selector `3134566563840 p₀ q₅ h⁵⁰`, and the
weight-sixty lambda selector `172186884 p₀ q₄ h⁵⁶` are preserved and
not cleared to zero.  No total-degree or twice-prime theorem is used.
A constant scale has no finite root, so no root-jet packet exists at
this scale.  Both the vanishing and the nonzero constant branches of
`λ` and of the weight-sixty and weight-sixty-five defects are kept.
The packet does not close the leaf: unused Jacobian coefficients start
at degree `1`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section ScaleZeroTwelfthDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/


variable [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- Strongest exact twelfth residual after the constant-scale source
bridge: the cleared weight-sixty-five sextic/decic defect is a scalar
times `h⁶⁵`.  The weight-fifty-five kappa residual and the weight-sixty
lambda residual are preserved.  Both the vanishing and the nonzero
values of `λ` are permitted. -/
theorem scaleZero_twelfthClearedDefect_exists_C_610
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda alpha gamma delta eps zeta eta theta iota kappa mu nu
        xi : k),
      (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedSecondDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (q.coeff 8) lambda =
        Polynomial.C alpha * (Polynomial.C t) ^ 10 ∧
      localClearedThirdDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (q.coeff 8) (q.coeff 7) lambda =
        Polynomial.C gamma * (Polynomial.C t) ^ 15 ∧
      localClearedFourthDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (q.coeff 8) (q.coeff 7) (q.coeff 6)
          lambda =
        Polynomial.C delta * (Polynomial.C t) ^ 20 ∧
      localClearedFifthDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) lambda =
        Polynomial.C eps * (Polynomial.C t) ^ 25 ∧
      localClearedSixthDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda =
        Polynomial.C zeta * (Polynomial.C t) ^ 30 ∧
      localClearedSeventhDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 35 ∧
      localClearedEighthDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) lambda =
        Polynomial.C theta * (Polynomial.C t) ^ 40 ∧
      localClearedNinthDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C iota * (Polynomial.C t) ^ 45 ∧
      localClearedTenthDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) (q.coeff 0) lambda =
        Polynomial.C kappa * (Polynomial.C t) ^ 50 ∧
      localClearedEleventhDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C mu * (Polynomial.C t) ^ 55 ∧
      localClearedTwelfthDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C nu * (Polynomial.C t) ^ 60 ∧
      localClearedThirteenthDefect610 (Polynomial.C t) (p.coeff 5)
          (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
          (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C xi * (Polynomial.C t) ^ 65 := by
  obtain ⟨lambda, alpha, gamma, delta, eps, zeta, eta, theta, iota, kappa,
      mu, nu, hN, halpha, hgamma, hdelta, heps, hzeta, heta, htheta,
      hiota, hkappa, hmu, hnu⟩ :=
    scaleZero_eleventhClearedDefect_exists_C_610 hp hq hD ht hH hp6 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨xi, hxi⟩ :=
    nonzeroFace610_thirteenthDefectPowerRelation p q H (Polynomial.C t) j
      lambda hp hq hh0 hH hp6 hq10 hN hD
  exact ⟨lambda, alpha, gamma, delta, eps, zeta, eta, theta, iota, kappa,
    mu, nu, xi, hN, halpha, hgamma, hdelta, heps, hzeta, heta, htheta,
    hiota, hkappa, hmu, hnu, hxi⟩


set_option maxHeartbeats 64000000 in
/-- Source-facing twelfth residual packet for a normalized scale-zero
`(6,10)` pair.  The constants `λ`, `ν`, and `ξ` may vanish, and the
weight-sixty lambda first integral remains a ground constant times
`h⁶⁰`. -/
theorem normalized610ScaleZero_exists_twelfthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda nu xi : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5) *
            H ^ 2 -
        (3 : k[X]) *
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9) =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedTwelfthDefect610 (Polynomial.C t)
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
        Polynomial.C nu * (Polynomial.C t) ^ 60 ∧
      localClearedThirteenthDefect610 (Polynomial.C t)
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
        Polynomial.C xi * (Polynomial.C t) ^ 65 := by
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  obtain ⟨t, ht, hHsq⟩ :=
    scaleZero_exists_constantSquareRoot_610 hH hHdegree
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨lambda, _a, _g, _d, _e, _z, _et, _th, _iot, _ka, _mu, nu, xi,
      hN, _hM, _hT, _hU, _hV, _hW, _hX, _hY, _hI, _hZ, _hJ, hnu, hxi⟩ :=
    scaleZero_twelfthClearedDefect_exists_C_610 hp hq hD ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
  exact ⟨t, lambda, nu, xi, ht, hHsq,
    by simpa only [p, q] using hN,
    by simpa only [p, q] using hnu,
    by simpa only [p, q] using hxi⟩


set_option maxHeartbeats 64000000 in
/-- At scale zero the weight-sixty-five defect is a literal ground-field
constant. -/
theorem normalized610ScaleZero_twelfthClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda xi : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedThirteenthDefect610 (Polynomial.C t)
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
        Polynomial.C xi := by
  obtain ⟨t, lambda, _nu, xi, ht, hHsq, _hN, _hY, hZ⟩ :=
    normalized610ScaleZero_exists_twelfthClearedDefect hsource
  refine ⟨t, lambda, xi * t ^ 65, ht, hHsq, ?_⟩
  have hconst :
      localClearedThirteenthDefect610 (Polynomial.C t)
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
        Polynomial.C (xi * t ^ 65) := by
    rw [hZ, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) xi (t ^ 65)).symm
  exact hconst


set_option maxHeartbeats 64000000 in
/-- Newton degree of the twelfth cleared sextic/decic defect at scale
zero. -/
theorem normalized610ScaleZero_twelfthClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedThirteenthDefect610 (Polynomial.C t)
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
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, xi, ht, hHsq, hZ⟩ :=
    normalized610ScaleZero_twelfthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hZ]
  exact (natDegree_C xi).le


set_option maxHeartbeats 64000000 in
/-- The eleventh packet's exact residual selector `172186884 p₀ q₄ h⁵⁶`
remains available on the twelfth packet. -/
theorem normalized610ScaleZero_eleventhSourceResidual_preserved
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda nu : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (172186884 : k[X]) * p.coeff 0 * q.coeff 4 * h0 ^ 56 =
        Polynomial.C nu -
          (localClearedTwelfthDefect610 h0 (p.coeff 5) (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
              (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
              lambda -
            (172186884 : k[X]) * p.coeff 0 * q.coeff 4 * h0 ^ 56) :=
  normalized610ScaleZero_eleventhSourceResidual hsource


set_option maxHeartbeats 64000000 in
/-- Exact twelfth residual selector: `6291456 p₀ q₃ h⁶²` differs from a
polynomial in the remaining thirteenth-defect monomials by a ground
constant. -/
theorem normalized610ScaleZero_twelfthSourceResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda xi : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (6291456 : k[X]) * p.coeff 0 * q.coeff 3 * h0 ^ 62 =
        Polynomial.C xi -
          (localClearedThirteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
              (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
              lambda -
            (6291456 : k[X]) * p.coeff 0 * q.coeff 3 * h0 ^ 62) := by
  dsimp only
  obtain ⟨t, lambda, xi, ht, hHsq, hZ⟩ :=
    normalized610ScaleZero_twelfthClearedDefect_exists_C hsource
  refine ⟨t, lambda, xi, ht, hHsq, ?_⟩
  rw [hZ]
  ring


set_option maxHeartbeats 64000000 in
/-- Aligned/nonzero split of the scale-zero twelfth cleared defect: it
vanishes, or it is a nonzero ground-field constant. -/
theorem normalized610ScaleZero_twelfthClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let W :=
        localClearedThirteenthDefect610 (Polynomial.C t)
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
          lambda
      W = 0 ∨ ∃ xi : k, xi ≠ 0 ∧ W = Polynomial.C xi := by
  dsimp only
  obtain ⟨t, lambda, xi, ht, hHsq, hZ⟩ :=
    normalized610ScaleZero_twelfthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  by_cases hxi : xi = 0
  · left
    simpa only [hxi, Polynomial.C_0] using hZ
  · exact Or.inr ⟨xi, hxi, hZ⟩

set_option maxHeartbeats 64000000 in
/-- Explicit zero/nonzero constant branches of both the discriminator
and the weight-sixty-five defect.  The weight-sixty lambda defect
remains a ground constant. -/
theorem normalized610ScaleZero_twelfthClearedDefectBranches
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda nu xi : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let N :=
        (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9
      let I :=
        localClearedTwelfthDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
      let W :=
        localClearedThirteenthDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      I = Polynomial.C nu ∧
      W = Polynomial.C xi ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (nu = 0 ∧ I = 0 ∨
        nu ≠ 0 ∧ I = Polynomial.C nu) ∧
      (xi = 0 ∧ W = 0 ∨
        xi ≠ 0 ∧ W = Polynomial.C xi) := by
  dsimp only
  obtain ⟨t, lambda, nu0, xi0, ht, hHsq, hN, hYpow, hZpow⟩ :=
    normalized610ScaleZero_exists_twelfthClearedDefect hsource
  let nu : k := nu0 * t ^ 60
  let xi : k := xi0 * t ^ 65
  have hY :
      localClearedTwelfthDefect610 (Polynomial.C t)
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
        Polynomial.C nu := by
    rw [hYpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) nu0 (t ^ 60)).symm
  have hZ :
      localClearedThirteenthDefect610 (Polynomial.C t)
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
        Polynomial.C xi := by
    rw [hZpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) xi0 (t ^ 65)).symm
  refine ⟨t, lambda, nu, xi, ht, hHsq, hN, hY, hZ, ?_, ?_, ?_⟩
  · by_cases hlambda : lambda = 0
    · left
      refine ⟨hlambda, ?_⟩
      simpa only [hlambda, Polynomial.C_0, zero_mul] using hN
    · right
      refine ⟨hlambda, ?_⟩
      have hNconst :
          (5 : k[X]) *
                ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
                  H ^ 2 -
              (3 : k[X]) *
                ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
            Polynomial.C (lambda * t ^ 9) := by
        rw [hN, ← Polynomial.C_pow]
        exact (map_mul (Polynomial.C : k →+* k[X]) lambda (t ^ 9)).symm
      exact hNconst
  · by_cases hnu : nu = 0
    · left
      refine ⟨hnu, ?_⟩
      simpa only [hnu, Polynomial.C_0] using hY
    · exact Or.inr ⟨hnu, hY⟩
  · by_cases hxi : xi = 0
    · left
      refine ⟨hxi, ?_⟩
      simpa only [hxi, Polynomial.C_0] using hZ
    · exact Or.inr ⟨hxi, hZ⟩


set_option maxHeartbeats 64000000 in
/-- Aligned branch `N = 0`: the weight-sixty-five defect is still a
ground constant, now with `λ = 0`. -/
theorem normalized610ScaleZero_twelfthClearedDefect_of_aligned
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (haligned :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t xi : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedThirteenthDefect610 (Polynomial.C t)
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
        Polynomial.C xi := by
  obtain ⟨t, lambda, _nu, xi0, ht, hHsq, hN, _hY, hZpow⟩ :=
    normalized610ScaleZero_exists_twelfthClearedDefect hsource
  have ht9 : (Polynomial.C t : k[X]) ^ 9 ≠ 0 :=
    pow_ne_zero 9 (Polynomial.C_ne_zero.mpr ht)
  have hlambda : lambda = 0 := by
    have hmul : Polynomial.C lambda * (Polynomial.C t) ^ 9 = 0 :=
      hN.symm.trans haligned
    have hC : Polynomial.C lambda = 0 :=
      (mul_eq_zero.mp hmul).resolve_right ht9
    exact Polynomial.C_eq_zero.mp hC
  refine ⟨t, xi0 * t ^ 65, ht, hHsq, ?_⟩
  have hZ :
      localClearedThirteenthDefect610 (Polynomial.C t)
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
        Polynomial.C (xi0 * t ^ 65) := by
    rw [← hlambda, hZpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) xi0 (t ^ 65)).symm
  exact hZ


set_option maxHeartbeats 64000000 in
/-- Nonzero discriminator branch: `λ ≠ 0` and the weight-sixty-five
defect is still a ground constant. -/
theorem normalized610ScaleZero_twelfthClearedDefect_of_nonzero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (hnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda xi : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5) *
            H ^ 2 -
        (3 : k[X]) *
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9) =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedThirteenthDefect610 (Polynomial.C t)
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
        Polynomial.C xi := by
  obtain ⟨t, lambda, _nu, xi0, ht, hHsq, hN, _hY, hZpow⟩ :=
    normalized610ScaleZero_exists_twelfthClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro hzero
    apply hnonzero
    simpa only [hzero, Polynomial.C_0, zero_mul] using hN
  refine ⟨t, lambda, xi0 * t ^ 65, ht, hlambda, hHsq, hN, ?_⟩
  have hZ :
      localClearedThirteenthDefect610 (Polynomial.C t)
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
        Polynomial.C (xi0 * t ^ 65) := by
    rw [hZpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) xi0 (t ^ 65)).symm
  exact hZ

end ScaleZeroTwelfthDefect610

end Max11DegreeRoutes
end
