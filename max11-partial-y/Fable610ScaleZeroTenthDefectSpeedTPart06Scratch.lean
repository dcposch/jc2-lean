import Fable610ScaleZeroTenthDefectSpeedTPart05Scratch

/-! # Scale-zero tenth cleared defect for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroNinthDefectScratch` on the constant core
`H = (C t)²`.  The ninth packet already forces the discriminator `N` and
the weight-fifty defect `ι` to ground constants, including the exact
selector `18 q₀ h⁵⁰`.  This file consumes the next unused Keller
coefficient, the degree-`4` Jacobian row

```
(p₄)' (1 q₁) + (p₃)' (2 q₂) + (p₂)' (3 q₃) + (p₁)' (4 q₄) + (p₀)' (5 q₅)
  - (5 p₅) q₀' - (4 p₄) q₁' - (3 p₃) q₂' - (2 p₂) q₃' - (1 p₁) q₄' = 0
```

of the same monic depression.  After the sextic change that kills `z⁵`,
that row is
`5 S E' + 4 T D' + 3 U C' + 2 V B' + W A' - D T' - 2 C U' - 3 B V'
- 4 A W' = 0`.  The corresponding first integral `κ` clears to the
weight-fifty-five polynomial defect, and at scale zero that defect is
again a ground-field constant.

This file supersedes the unverified `Grok610ScaleZeroTenthDefectScratch`
attempt.  Its `κ` formula, weight-fifty-five clearing, and packet wiring
were re-derived independently and port unchanged; the derivation-in-zero
reduction is completed with the full constant-derivative kill set
(`d (385/31104) = 0` through `d (A⁵)`), whose absence left opaque
derivative atoms in the final `linear_combination`, and the aligned
`λ = 0` specialization states the literal `132`-monomial residue instead
of a reflexive identity.

The degree-`5` iota first integral and the exact `18 q₀ h⁵⁰` residual
are preserved and not cleared to zero.  No total-degree or twice-prime
theorem is used.  A constant scale has no finite root, so the scale-two
eleventh-face jet is unavailable.  Both the vanishing and the nonzero
constant branches of `λ` and of the weight-fifty and weight-fifty-five
defects are kept.  The packet does not close the leaf: unused Jacobian
coefficients start at degree `3`.
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

section ScaleZeroTenthDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/

variable [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- Strongest exact tenth residual after the constant-scale source bridge:
the cleared weight-fifty-five sextic/decic defect is a scalar times `h⁵⁵`.
The weight-fifty iota residual `18 q₀ h⁵⁰` is preserved.  Both the
vanishing and the nonzero values of `λ` are permitted. -/
theorem scaleZero_tenthClearedDefect_exists_C_610
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda alpha gamma delta eps zeta eta theta iota kappa mu : k),
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
        Polynomial.C mu * (Polynomial.C t) ^ 55 := by
  obtain ⟨lambda, alpha, gamma, delta, eps, zeta, eta, theta, iota, kappa, hN,
      halpha, hgamma, hdelta, heps, hzeta, heta, htheta, hiota, hkappa⟩ :=
    scaleZero_ninthClearedDefect_exists_C_610 hp hq hD ht hH hp6 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨mu, hmu⟩ :=
    nonzeroFace610_eleventhDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  exact ⟨lambda, alpha, gamma, delta, eps, zeta, eta, theta, iota, kappa, mu, hN,
    halpha, hgamma, hdelta, heps, hzeta, heta, htheta, hiota, hkappa, hmu⟩

set_option maxHeartbeats 64000000 in
/-- Source-facing tenth residual packet for a normalized scale-zero
`(6,10)` pair.  The constants `λ` and `μ` may vanish, and the degree-`5`
iota first integral remains a ground constant times `h⁵⁰`. -/
theorem normalized610ScaleZero_exists_tenthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda iota mu : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedTenthDefect610 (Polynomial.C t)
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
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda =
        Polynomial.C iota * (Polynomial.C t) ^ 50 ∧
      localClearedEleventhDefect610 (Polynomial.C t)
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
        Polynomial.C mu * (Polynomial.C t) ^ 55 := by
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
  obtain ⟨lambda, _a, _g, _d, _e, _z, _et, _th, _iot, kappa, mu, hN, _hM, _hT,
      _hU, _hV, _hW, _hX, _hY, _hI, hZ, hmu⟩ :=
    scaleZero_tenthClearedDefect_exists_C_610 hp hq hD ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
  exact ⟨t, lambda, kappa, mu, ht, hHsq,
    by simpa only [p, q] using hN,
    by simpa only [p, q] using hZ,
    by simpa only [p, q] using hmu⟩

set_option maxHeartbeats 64000000 in
/-- At scale zero the weight-fifty-five defect is a literal ground-field
constant. -/
theorem normalized610ScaleZero_tenthClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda mu : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedEleventhDefect610 (Polynomial.C t)
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
        Polynomial.C mu := by
  obtain ⟨t, lambda, _iota, mu, ht, hHsq, _hN, _hI, hY⟩ :=
    normalized610ScaleZero_exists_tenthClearedDefect hsource
  refine ⟨t, lambda, mu * t ^ 55, ht, hHsq, ?_⟩
  have hconst :
      localClearedEleventhDefect610 (Polynomial.C t)
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
        Polynomial.C (mu * t ^ 55) := by
    rw [hY, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) mu (t ^ 55)).symm
  exact hconst

set_option maxHeartbeats 64000000 in
/-- Newton degree of the tenth cleared sextic/decic defect at scale zero. -/
theorem normalized610ScaleZero_tenthClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedEleventhDefect610 (Polynomial.C t)
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
  obtain ⟨t, lambda, mu, ht, hHsq, hY⟩ :=
    normalized610ScaleZero_tenthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hY]
  exact (natDegree_C mu).le

set_option maxHeartbeats 64000000 in
/-- The ninth packet's exact residual selector `18 q₀ h⁵⁰` remains
available on the tenth packet. -/
theorem normalized610ScaleZero_ninthSourceResidual_preserved
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda theta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (18 : k[X]) * q.coeff 0 * h0 ^ 50 =
        Polynomial.C theta -
          (localClearedTenthDefect610 h0 (p.coeff 5) (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
              (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (q.coeff 0) lambda -
            (18 : k[X]) * q.coeff 0 * h0 ^ 50) :=
  normalized610ScaleZero_ninthSourceResidual hsource

set_option maxHeartbeats 64000000 in
/-- Exact tenth residual selector: `3134566563840 p₀ q₅ h⁵⁰` differs from a
polynomial in the remaining tenth-defect monomials by a ground constant. -/
theorem normalized610ScaleZero_tenthSourceResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda mu : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (3134566563840 : k[X]) * p.coeff 0 * q.coeff 5 * h0 ^ 50 =
        Polynomial.C mu -
          (localClearedEleventhDefect610 h0 (p.coeff 5) (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
              (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
              lambda -
            (3134566563840 : k[X]) * p.coeff 0 * q.coeff 5 * h0 ^ 50) := by
  dsimp only
  obtain ⟨t, lambda, mu, ht, hHsq, hY⟩ :=
    normalized610ScaleZero_tenthClearedDefect_exists_C hsource
  refine ⟨t, lambda, mu, ht, hHsq, ?_⟩
  rw [hY]
  ring

set_option maxHeartbeats 64000000 in
/-- Aligned/nonzero split of the scale-zero tenth cleared defect: it
vanishes, or it is a nonzero ground-field constant. -/
theorem normalized610ScaleZero_tenthClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let W :=
        localClearedEleventhDefect610 (Polynomial.C t)
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
      W = 0 ∨ ∃ mu : k, mu ≠ 0 ∧ W = Polynomial.C mu := by
  dsimp only
  obtain ⟨t, lambda, mu, ht, hHsq, hY⟩ :=
    normalized610ScaleZero_tenthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  by_cases hmu : mu = 0
  · left
    simpa only [hmu, Polynomial.C_0] using hY
  · exact Or.inr ⟨mu, hmu, hY⟩

set_option maxHeartbeats 64000000 in
/-- Explicit zero/nonzero constant branches of both the discriminator and
the weight-fifty-five defect.  The weight-fifty iota defect remains a
ground constant. -/
theorem normalized610ScaleZero_tenthClearedDefectBranches
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda iota mu : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let N :=
        (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9
      let I :=
        localClearedTenthDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (q.coeff 0) lambda
      let W :=
        localClearedEleventhDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      I = Polynomial.C iota ∧
      W = Polynomial.C mu ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (iota = 0 ∧ I = 0 ∨
        iota ≠ 0 ∧ I = Polynomial.C iota) ∧
      (mu = 0 ∧ W = 0 ∨
        mu ≠ 0 ∧ W = Polynomial.C mu) := by
  dsimp only
  obtain ⟨t, lambda, iota0, mu0, ht, hHsq, hN, hIpow, hYpow⟩ :=
    normalized610ScaleZero_exists_tenthClearedDefect hsource
  let iota : k := iota0 * t ^ 50
  let mu : k := mu0 * t ^ 55
  have hI :
      localClearedTenthDefect610 (Polynomial.C t)
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
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda =
        Polynomial.C iota := by
    rw [hIpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) iota0 (t ^ 50)).symm
  have hY :
      localClearedEleventhDefect610 (Polynomial.C t)
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
        Polynomial.C mu := by
    rw [hYpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) mu0 (t ^ 55)).symm
  refine ⟨t, lambda, iota, mu, ht, hHsq, hN, hI, hY, ?_, ?_, ?_⟩
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
  · by_cases hiota : iota = 0
    · left
      refine ⟨hiota, ?_⟩
      simpa only [hiota, Polynomial.C_0] using hI
    · exact Or.inr ⟨hiota, hI⟩
  · by_cases hmu : mu = 0
    · left
      refine ⟨hmu, ?_⟩
      simpa only [hmu, Polynomial.C_0] using hY
    · exact Or.inr ⟨hmu, hY⟩

set_option maxHeartbeats 64000000 in
/-- Aligned branch `N = 0`: the weight-fifty-five defect is still a ground
constant, now with `λ = 0`. -/
theorem normalized610ScaleZero_tenthClearedDefect_of_aligned
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (haligned :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t mu : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedEleventhDefect610 (Polynomial.C t)
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
        Polynomial.C mu := by
  obtain ⟨t, lambda, _iota, mu0, ht, hHsq, hN, _hI, hYpow⟩ :=
    normalized610ScaleZero_exists_tenthClearedDefect hsource
  have ht9 : (Polynomial.C t : k[X]) ^ 9 ≠ 0 :=
    pow_ne_zero 9 (Polynomial.C_ne_zero.mpr ht)
  have hlambda : lambda = 0 := by
    have hmul : Polynomial.C lambda * (Polynomial.C t) ^ 9 = 0 :=
      hN.symm.trans haligned
    have hC : Polynomial.C lambda = 0 :=
      (mul_eq_zero.mp hmul).resolve_right ht9
    exact Polynomial.C_eq_zero.mp hC
  refine ⟨t, mu0 * t ^ 55, ht, hHsq, ?_⟩
  have hY :
      localClearedEleventhDefect610 (Polynomial.C t)
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
        Polynomial.C (mu0 * t ^ 55) := by
    rw [← hlambda, hYpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) mu0 (t ^ 55)).symm
  exact hY

set_option maxHeartbeats 64000000 in
/-- Nonzero discriminator branch: `λ ≠ 0` and the weight-fifty-five defect
is still a ground constant. -/
theorem normalized610ScaleZero_tenthClearedDefect_of_nonzero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (hnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda mu : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedEleventhDefect610 (Polynomial.C t)
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
        Polynomial.C mu := by
  obtain ⟨t, lambda, _iota, mu0, ht, hHsq, hN, _hI, hYpow⟩ :=
    normalized610ScaleZero_exists_tenthClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro hzero
    apply hnonzero
    simpa only [hzero, Polynomial.C_0, zero_mul] using hN
  refine ⟨t, lambda, mu0 * t ^ 55, ht, hlambda, hHsq, hN, ?_⟩
  have hY :
      localClearedEleventhDefect610 (Polynomial.C t)
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
        Polynomial.C (mu0 * t ^ 55) := by
    rw [hYpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) mu0 (t ^ 55)).symm
  exact hY

end ScaleZeroTenthDefect610

end Max11DegreeRoutes
end
