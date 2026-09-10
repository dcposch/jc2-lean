import Fable610ScaleZeroEleventhDefectSpeedTPart01Scratch

/-! # Scale-zero eleventh cleared defect for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Fable610ScaleZeroTenthDefectScratch` on the constant core
`H = (C t)²`.  The tenth packet already forces the discriminator `N`, the
weight-fifty defect `ι`, and the weight-fifty-five defect `κ` to ground
constants, including the exact selectors `18 q₀ h⁵⁰` and
`3134566563840 p₀ q₅ h⁵⁰`.  This file consumes the next unused Keller
coefficient, the degree-`3` Jacobian row

```
(p₃)' (1 q₁) + (p₂)' (2 q₂) + (p₁)' (3 q₃) + (p₀)' (4 q₄)
  - (4 p₄) q₀' - (3 p₃) q₁' - (2 p₂) q₂' - (1 p₁) q₃' = 0
```

of the same monic depression.  After the sextic change that kills `z⁵`,
that row is
`4 T E' + 3 U D' + 2 V C' + W B' - D U' - 2 C V' - 3 B W' - 4 A X' = 0`.
The derivative `X'` is eliminated through the degree-`5` row, so the
first integral `λ` of the degree-`3` row uses only the second- through
ninth-face integrals; it clears to the weight-sixty polynomial defect,
and at scale zero that defect is again a ground-field constant.

The `λ` formula, its weight-sixty clearing by `258280326 h⁶⁰`, the
solved derivative forms, and the aligned `179`-monomial specialization
were derived and cross-checked independently (closedness of the reduced
row `1`-form, the identity `d λ = (1/6) · row`, and a rational
end-to-end evaluation of the cleared polynomial).  The
derivation-in-zero reduction keeps the sub-residuals opaque so the
tower hypotheses fire, and supplies the complete constant-derivative
kill set from `d (1/4) = 0` through `d (385/7776) = 0` and `d (A⁶)`,
`d (B⁴)`, `d (E²)`.

The degree-`5` iota first integral, the exact `18 q₀ h⁵⁰` residual, and
the degree-`4` kappa selector `3134566563840 p₀ q₅ h⁵⁰` are preserved
and not cleared to zero.  No total-degree or twice-prime theorem is
used.  A constant scale has no finite root, so no root-jet packet
exists at this scale.  Both the vanishing and the nonzero constant
branches of `λ` and of the weight-fifty-five and weight-sixty defects
are kept.  The packet does not close the leaf: unused Jacobian
coefficients start at degree `2`.
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

section ScaleZeroEleventhDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/


section Depression610Twelfth

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 10. -/
private abbrev fable610eleventhSpeedT_speedLambdaResidual610Scaled60_chunk01 (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    (13365 / 256 : F) * h ^ 5 * nL * nA ^ 4 * nB
    - (3645 / 32 : F) * h ^ 5 * nL * nA ^ 3 * nD
    - (10935 / 64 : F) * h ^ 5 * nL * nA ^ 2 * nB * nC
    - (135 / 4 : F) * h ^ 5 * nL * nA * nB ^ 3
    + (1215 / 256 : F) * h ^ 5 * nL * nA * nB * nE
    + (32805 / 128 : F) * h ^ 5 * nL * nA * nC * nD
    + (1215 / 16 : F) * h ^ 5 * nL * nB ^ 2 * nD
    + (32805 / 512 : F) * h ^ 5 * nL * nB * nC ^ 2
    - (729 / 128 : F) * h ^ 5 * nL * nD * nE
    - (10395 / 1024 : F) * nA ^ 6

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 20. -/
private abbrev fable610eleventhSpeedT_speedLambdaResidual610Scaled60_chunk02 (acc : F) (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    + (8019 / 256 : F) * nA ^ 5 * nP
    + (66825 / 1024 : F) * nA ^ 4 * nC
    - (3645 / 1024 : F) * nA ^ 4 * nR
    + (2475 / 32 : F) * nA ^ 3 * nB ^ 2
    - (2835 / 16 : F) * nA ^ 3 * nB * nQ
    - (10935 / 64 : F) * nA ^ 3 * nC * nP
    - (675 / 256 : F) * nA ^ 3 * nE
    + (1215 / 512 : F) * nA ^ 3 * nT
    - (1215 / 8 : F) * nA ^ 2 * nB ^ 2 * nP
    - (2025 / 8 : F) * nA ^ 2 * nB * nD

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 30. -/
private abbrev fable610eleventhSpeedT_speedLambdaResidual610Scaled60_chunk03 (acc : F) (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    + (18225 / 256 : F) * nA ^ 2 * nB * nS
    - (54675 / 512 : F) * nA ^ 2 * nC ^ 2
    + (32805 / 2048 : F) * nA ^ 2 * nC * nR
    + (25515 / 64 : F) * nA ^ 2 * nD * nQ
    + (3645 / 512 : F) * nA ^ 2 * nE * nP
    - (2187 / 2048 : F) * nA ^ 2 * nV
    - (2025 / 16 : F) * nA * nB ^ 2 * nC
    + (1215 / 128 : F) * nA * nB ^ 2 * nR
    + (25515 / 64 : F) * nA * nB * nC * nQ
    + (3645 / 8 : F) * nA * nB * nD * nP

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 40. -/
private abbrev fable610eleventhSpeedT_speedLambdaResidual610Scaled60_chunk04 (acc : F) (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    - (729 / 64 : F) * nA * nB * nU
    + (98415 / 512 : F) * nA * nC ^ 2 * nP
    + (6075 / 1024 : F) * nA * nC * nE
    - (2187 / 256 : F) * nA * nC * nT
    + (6075 / 32 : F) * nA * nD ^ 2
    - (10935 / 64 : F) * nA * nD * nS
    - (729 / 1024 : F) * nA * nE * nR
    - (25 / 4 : F) * nB ^ 4
    + (315 / 8 : F) * nB ^ 3 * nQ
    + (3645 / 32 : F) * nB ^ 2 * nC * nP

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 50. -/
private abbrev fable610eleventhSpeedT_speedLambdaResidual610Scaled60_chunk05 (acc : F) (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    + (225 / 128 : F) * nB ^ 2 * nE
    - (81 / 32 : F) * nB ^ 2 * nT
    + (6075 / 32 : F) * nB * nC * nD
    - (10935 / 128 : F) * nB * nC * nS
    - (729 / 32 : F) * nB * nD * nR
    - (567 / 64 : F) * nB * nE * nQ
    + (81 / 512 : F) * nB * nW
    + (54675 / 2048 : F) * nC ^ 3
    - (19683 / 2048 : F) * nC ^ 2 * nR
    - (15309 / 32 : F) * nC * nD * nQ

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 56. -/
private abbrev fable610eleventhSpeedT_speedLambdaResidual610Scaled60_chunk06 (acc : F) (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    - (2187 / 256 : F) * nC * nE * nP
    + (6561 / 2048 : F) * nC * nV
    - (2187 / 8 : F) * nD ^ 2 * nP
    + (2187 / 64 : F) * nD * nU
    - (135 / 2048 : F) * nE ^ 2
    + (243 / 512 : F) * nE * nT

set_option maxHeartbeats 64000000 in
/-- SPEED (recipe R2, `scripts/coord/LEAN_SPEED_REPORT.md` §7): the weight-`60`
clearing of `lambdaResidual610` carried out on the *atoms* rather than on the fully
substituted source polynomials.  `lambdaResidual610` is weighted homogeneous, so
substituting `X_i = n_i / (d_i h^(e_i))` makes `258280326 * h^60 * lambdaResidual610`
a polynomial in `h, n_*` — 56 monomials. -/
def speedLambdaResidual610Scaled60 (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    fable610eleventhSpeedT_speedLambdaResidual610Scaled60_chunk06
      (fable610eleventhSpeedT_speedLambdaResidual610Scaled60_chunk05
      (fable610eleventhSpeedT_speedLambdaResidual610Scaled60_chunk04
      (fable610eleventhSpeedT_speedLambdaResidual610Scaled60_chunk03
      (fable610eleventhSpeedT_speedLambdaResidual610Scaled60_chunk02
      (fable610eleventhSpeedT_speedLambdaResidual610Scaled60_chunk01 h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW

set_option maxHeartbeats 64000000 in
/-- The atom-level clearing: one `field_simp` over 15 atomic variables in
place of the single enormous `field_simp` on the substituted rational function. -/
theorem speedLambdaResidual610Scaled60_eq (h : F) (hh : h ≠ 0) (nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) :
    (258280326 : F) * h ^ 60 *
        lambdaResidual610
          (nL / 3)
          (nA / (12 * h ^ 10))
          (nB / (54 * h ^ 15))
          (nC / (144 * h ^ 20))
          (nD / (324 * h ^ 25))
          (nE / (46656 * h ^ 30))
          (nP / (4 * h ^ 10))
          (nQ / (9 * h ^ 15))
          (nR / (432 * h ^ 20))
          (nS / (216 * h ^ 25))
          (nT / (7776 * h ^ 30))
          (nU / (11664 * h ^ 35))
          (nV / (186624 * h ^ 40))
          (nW / (5038848 * h ^ 45)) =
      speedLambdaResidual610Scaled60 h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW := by
  have hd2 : (2 : F) ≠ 0 := by norm_num
  have hd3 : (3 : F) ≠ 0 := by norm_num
  have hd4 : (4 : F) ≠ 0 := by norm_num
  have hd9 : (9 : F) ≠ 0 := by norm_num
  have hd12 : (12 : F) ≠ 0 := by norm_num
  have hd54 : (54 : F) ≠ 0 := by norm_num
  have hd144 : (144 : F) ≠ 0 := by norm_num
  have hd216 : (216 : F) ≠ 0 := by norm_num
  have hd324 : (324 : F) ≠ 0 := by norm_num
  have hd432 : (432 : F) ≠ 0 := by norm_num
  have hd7776 : (7776 : F) ≠ 0 := by norm_num
  have hd11664 : (11664 : F) ≠ 0 := by norm_num
  have hd46656 : (46656 : F) ≠ 0 := by norm_num
  have hd186624 : (186624 : F) ≠ 0 := by norm_num
  have hd5038848 : (5038848 : F) ≠ 0 := by norm_num
  have hp10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hp15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hp20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hp25 : h ^ 25 ≠ 0 := pow_ne_zero 25 hh
  have hp30 : h ^ 30 ≠ 0 := pow_ne_zero 30 hh
  have hp35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hp40 : h ^ 40 ≠ 0 := pow_ne_zero 40 hh
  have hp45 : h ^ 45 ≠ 0 := pow_ne_zero 45 hh
  simp only [alphaResidual610, betaResidual610, deltaResidual610, epsilonResidual610, etaResidual610, gammaResidual610, lambdaResidual610, thetaResidual610, zetaResidual610, speedLambdaResidual610Scaled60]
  field_simp
  ring


end Depression610Twelfth

end ScaleZeroEleventhDefect610
end Max11DegreeRoutes
end
