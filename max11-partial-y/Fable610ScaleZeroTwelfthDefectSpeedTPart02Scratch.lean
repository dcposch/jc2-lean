import Fable610ScaleZeroTwelfthDefectSpeedTPart01Scratch

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


section Depression610Thirteenth

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 10. -/
private abbrev fable610twelfthSpeedT_speedMuResidual610Scaled65_chunk01 (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    - (7 / 81 : F) * h ^ 5 * nL * nA ^ 6
    + (140 / 243 : F) * h ^ 5 * nL * nA ^ 4 * nC
    + (4480 / 6561 : F) * h ^ 5 * nL * nA ^ 3 * nB ^ 2
    - (160 / 6561 : F) * h ^ 5 * nL * nA ^ 3 * nE
    - (5120 / 2187 : F) * h ^ 5 * nL * nA ^ 2 * nB * nD
    - (80 / 81 : F) * h ^ 5 * nL * nA ^ 2 * nC ^ 2
    - (2560 / 2187 : F) * h ^ 5 * nL * nA * nB ^ 2 * nC
    + (128 / 2187 : F) * h ^ 5 * nL * nA * nC * nE
    + (4096 / 2187 : F) * h ^ 5 * nL * nA * nD ^ 2
    - (10240 / 177147 : F) * h ^ 5 * nL * nB ^ 4

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 20. -/
private abbrev fable610twelfthSpeedT_speedMuResidual610Scaled65_chunk02 (acc : F) (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    + (1024 / 59049 : F) * h ^ 5 * nL * nB ^ 2 * nE
    + (4096 / 2187 : F) * h ^ 5 * nL * nB * nC * nD
    + (64 / 243 : F) * h ^ 5 * nL * nC ^ 3
    - (128 / 177147 : F) * h ^ 5 * nL * nE ^ 2
    - (280 / 729 : F) * nA ^ 5 * nB
    + (784 / 2187 : F) * nA ^ 5 * nQ
    + (2240 / 2187 : F) * nA ^ 4 * nB * nP
    + (5600 / 6561 : F) * nA ^ 4 * nD
    - (400 / 2187 : F) * nA ^ 4 * nS
    + (11200 / 6561 : F) * nA ^ 3 * nB * nC

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 30. -/
private abbrev fable610twelfthSpeedT_speedMuResidual610Scaled65_chunk03 (acc : F) (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    - (640 / 6561 : F) * nA ^ 3 * nB * nR
    - (4480 / 2187 : F) * nA ^ 3 * nC * nQ
    - (5120 / 2187 : F) * nA ^ 3 * nD * nP
    + (256 / 6561 : F) * nA ^ 3 * nU
    + (89600 / 177147 : F) * nA ^ 2 * nB ^ 3
    - (35840 / 19683 : F) * nA ^ 2 * nB ^ 2 * nQ
    - (2560 / 729 : F) * nA ^ 2 * nB * nC * nP
    - (3200 / 59049 : F) * nA ^ 2 * nB * nE
    + (1024 / 19683 : F) * nA ^ 2 * nB * nT
    - (6400 / 2187 : F) * nA ^ 2 * nC * nD

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 40. -/
private abbrev fable610twelfthSpeedT_speedMuResidual610Scaled65_chunk04 (acc : F) (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    + (640 / 729 : F) * nA ^ 2 * nC * nS
    + (512 / 2187 : F) * nA ^ 2 * nD * nR
    + (1792 / 19683 : F) * nA ^ 2 * nE * nQ
    - (128 / 177147 : F) * nA ^ 2 * nW
    - (40960 / 59049 : F) * nA * nB ^ 3 * nP
    - (102400 / 59049 : F) * nA * nB ^ 2 * nD
    + (10240 / 19683 : F) * nA * nB ^ 2 * nS
    - (3200 / 2187 : F) * nA * nB * nC ^ 2
    + (512 / 2187 : F) * nA * nB * nC * nR
    + (114688 / 19683 : F) * nA * nB * nD * nQ

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 50. -/
private abbrev fable610twelfthSpeedT_speedMuResidual610Scaled65_chunk05 (acc : F) (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    + (2048 / 19683 : F) * nA * nB * nE * nP
    - (1024 / 59049 : F) * nA * nB * nV
    + (1792 / 729 : F) * nA * nC ^ 2 * nQ
    + (4096 / 729 : F) * nA * nC * nD * nP
    - (1024 / 6561 : F) * nA * nC * nU
    + (5120 / 59049 : F) * nA * nD * nE
    - (8192 / 59049 : F) * nA * nD * nT
    - (2560 / 59049 : F) * nA * nE * nS
    - (51200 / 177147 : F) * nB ^ 3 * nC
    + (4096 / 177147 : F) * nB ^ 3 * nR

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 60. -/
private abbrev fable610twelfthSpeedT_speedMuResidual610Scaled65_chunk06 (acc : F) (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    + (28672 / 19683 : F) * nB ^ 2 * nC * nQ
    + (32768 / 19683 : F) * nB ^ 2 * nD * nP
    - (8192 / 177147 : F) * nB ^ 2 * nU
    + (1024 / 729 : F) * nB * nC ^ 2 * nP
    + (2560 / 59049 : F) * nB * nC * nE
    - (4096 / 59049 : F) * nB * nC * nT
    + (81920 / 59049 : F) * nB * nD ^ 2
    - (81920 / 59049 : F) * nB * nD * nS
    - (1024 / 177147 : F) * nB * nE * nR
    + (2560 / 2187 : F) * nC ^ 2 * nD

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 68. -/
private abbrev fable610twelfthSpeedT_speedMuResidual610Scaled65_chunk07 (acc : F) (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    - (1280 / 2187 : F) * nC ^ 2 * nS
    - (2048 / 6561 : F) * nC * nD * nR
    - (7168 / 59049 : F) * nC * nE * nQ
    + (512 / 177147 : F) * nC * nW
    - (229376 / 59049 : F) * nD ^ 2 * nQ
    - (8192 / 59049 : F) * nD * nE * nP
    + (4096 / 59049 : F) * nD * nV
    + (2048 / 177147 : F) * nE * nU

set_option maxHeartbeats 64000000 in
/-- SPEED (recipe R2, `scripts/coord/LEAN_SPEED_REPORT.md` §7): the weight-`65`
clearing of `muResidual610` carried out on the *atoms* rather than on the fully
substituted source polynomials.  `muResidual610` is weighted homogeneous, so
substituting `X_i = n_i / (d_i h^(e_i))` makes `12582912 * h^65 * muResidual610`
a polynomial in `h, n_*` — 68 monomials. -/
def speedMuResidual610Scaled65 (h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) : F :=
    fable610twelfthSpeedT_speedMuResidual610Scaled65_chunk07
      (fable610twelfthSpeedT_speedMuResidual610Scaled65_chunk06
      (fable610twelfthSpeedT_speedMuResidual610Scaled65_chunk05
      (fable610twelfthSpeedT_speedMuResidual610Scaled65_chunk04
      (fable610twelfthSpeedT_speedMuResidual610Scaled65_chunk03
      (fable610twelfthSpeedT_speedMuResidual610Scaled65_chunk02
      (fable610twelfthSpeedT_speedMuResidual610Scaled65_chunk01 h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW

set_option maxHeartbeats 64000000 in
/-- The atom-level clearing: one `field_simp` over 15 atomic variables in
place of the single enormous `field_simp` on the substituted rational function. -/
theorem speedMuResidual610Scaled65_eq (h : F) (hh : h ≠ 0) (nL nA nB nC nD nE nP nQ nR nS nT nU nV nW : F) :
    (12582912 : F) * h ^ 65 *
        muResidual610
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
      speedMuResidual610Scaled65 h nL nA nB nC nD nE nP nQ nR nS nT nU nV nW := by
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
  simp only [alphaResidual610, betaResidual610, deltaResidual610, epsilonResidual610, etaResidual610, gammaResidual610, muResidual610, thetaResidual610, zetaResidual610, speedMuResidual610Scaled65]
  field_simp
  ring


end Depression610Thirteenth

end ScaleZeroTwelfthDefect610
end Max11DegreeRoutes
end
