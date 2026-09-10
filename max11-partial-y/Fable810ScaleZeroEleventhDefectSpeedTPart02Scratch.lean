import Fable810ScaleZeroEleventhDefectSpeedTPart01Scratch

/-! # Scale-zero eleventh defect for the normalized `(8,10)`, `H = 0` leaf

The tenth-defect packet already makes the discriminator `N` a
ground-field constant and, after a square root of the core, clears the
first ten octic/decic defects to ground constants times `h¹⁴`, `h²¹`,
`h²⁸`, `h³⁵`, `h⁴²`, `h⁴⁹`, `h⁵⁶`, `h⁶³`, `h⁷⁰`, and `h⁷⁷`.  This file
consumes the next unused Keller coefficient of the same monic
octic-decic depression: the degree-`5` Jacobian row is
`6 R G' + 5 S F' + 4 T E' + 3 U D' + 2 V C' + W B'
- F S' - 2 E T' - 3 D U' - 4 C V' - 5 B W' - 6 A X' = 0`.  The
corresponding twelfth cleared polynomial defect of weight eighty-four
is likewise a ground-field constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  The same zero/nonzero split is recorded
for the weight-`84` defect itself.  Root-evaluation from a scale-two
face is unavailable, because a nonzero constant has no finite root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`4` residual of
the same monic depression.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

/-! ## Literal next Keller coefficient -/

section Depression810TwelfthClearing

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
private abbrev fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk01 (h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) : F :=
    (10395 / 8 : F) * h ^ 7 * nL * nA ^ 4 * nB
    - (693 : F) * h ^ 7 * nL * nA ^ 3 * nD
    - (2079 / 4 : F) * h ^ 7 * nL * nA ^ 2 * nB * nC
    + (189 / 2 : F) * h ^ 7 * nL * nA ^ 2 * nF
    - (5544 : F) * h ^ 7 * nL * nA * nB ^ 3
    + (189 : F) * h ^ 7 * nL * nA * nB * nE
    + (189 : F) * h ^ 7 * nL * nA * nC * nD
    + (3024 : F) * h ^ 7 * nL * nB ^ 2 * nD
    + (189 / 8 : F) * h ^ 7 * nL * nB * nC ^ 2
    - (27 / 4 : F) * h ^ 7 * nL * nB * nG

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
private abbrev fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk02 (acc : F) (h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    - (27 / 2 : F) * h ^ 7 * nL * nC * nF
    - (54 : F) * h ^ 7 * nL * nD * nE
    - (7315 / 64 : F) * nA ^ 6
    + (231 / 8 : F) * nA ^ 5 * nP
    + (5775 / 64 : F) * nA ^ 4 * nC
    - (231 / 16 : F) * nA ^ 4 * nR
    + (5775 : F) * nA ^ 3 * nB ^ 2
    - (1078 : F) * nA ^ 3 * nB * nQ
    - (77 / 4 : F) * nA ^ 3 * nC * nP
    - (385 / 8 : F) * nA ^ 3 * nE

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
private abbrev fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk03 (acc : F) (h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    + (7 / 2 : F) * nA ^ 3 * nT
    - (924 : F) * nA ^ 2 * nB ^ 2 * nP
    - (4620 : F) * nA ^ 2 * nB * nD
    + (105 : F) * nA ^ 2 * nB * nS
    - (1155 / 64 : F) * nA ^ 2 * nC ^ 2
    + (63 / 8 : F) * nA ^ 2 * nC * nR
    + (588 : F) * nA ^ 2 * nD * nQ
    + (21 / 2 : F) * nA ^ 2 * nE * nP
    + (105 / 32 : F) * nA ^ 2 * nG
    - (3 / 8 : F) * nA ^ 2 * nV

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
private abbrev fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk04 (acc : F) (h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    - (1155 : F) * nA * nB ^ 2 * nC
    + (252 : F) * nA * nB ^ 2 * nR
    + (294 : F) * nA * nB * nC * nQ
    + (672 : F) * nA * nB * nD * nP
    + (420 : F) * nA * nB * nF
    - (36 : F) * nA * nB * nU
    + (21 / 8 : F) * nA * nC ^ 2 * nP
    + (105 / 8 : F) * nA * nC * nE
    - (3 / 2 : F) * nA * nC * nT
    + (840 : F) * nA * nD ^ 2

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
private abbrev fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk05 (acc : F) (h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    - (60 : F) * nA * nD * nS
    - (9 / 2 : F) * nA * nE * nR
    - (84 : F) * nA * nF * nQ
    - (3 / 4 : F) * nA * nG * nP
    - (3080 : F) * nB ^ 4
    + (1568 : F) * nB ^ 3 * nQ
    + (84 : F) * nB ^ 2 * nC * nP
    + (210 : F) * nB ^ 2 * nE
    - (24 : F) * nB ^ 2 * nT
    + (420 : F) * nB * nC * nD

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
private abbrev fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk06 (acc : F) (h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    - (15 : F) * nB * nC * nS
    - (144 : F) * nB * nD * nR
    - (84 : F) * nB * nE * nQ
    - (48 : F) * nB * nF * nP
    + (1 : F) * nB * nW
    + (35 / 64 : F) * nC ^ 3
    - (9 / 16 : F) * nC ^ 2 * nR
    - (84 : F) * nC * nD * nQ
    - (3 / 2 : F) * nC * nE * nP
    - (15 / 32 : F) * nC * nG

set_option maxHeartbeats 64000000 in
/-- Accumulator chunk of at most ten monomials. -/
private abbrev fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk07 (acc : F) (h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) : F :=
    acc
    + (1 / 8 : F) * nC * nV
    - (96 : F) * nD ^ 2 * nP
    - (120 : F) * nD * nF
    + (24 : F) * nD * nU
    - (15 / 8 : F) * nE ^ 2
    + (1 : F) * nE * nT
    + (10 : F) * nF * nS
    + (3 / 8 : F) * nG * nR

set_option maxHeartbeats 64000000 in
/-- SPEED (recipe R2, `scripts/coord/LEAN_SPEED_REPORT.md` §7): the weight-`84`
clearing of `muResidual810` carried out on the *atoms* rather than on the fully
substituted source polynomials.  `muResidual810` is weighted homogeneous, so
substituting `X_i = n_i / (d_i h^(e_i))` makes `17179869184 * h^84 * muResidual810`
a polynomial in `h, n_*` — 68 monomials. -/
def speedMuResidual810Scaled84 (h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) : F :=
    fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk07
      (fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk06
      (fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk05
      (fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk04
      (fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk03
      (fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk02
      (fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk01 h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW) h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW

set_option maxHeartbeats 64000000 in
/-- The atom-level clearing: one `field_simp` over 17 atomic variables in
place of the single enormous `field_simp` on the substituted rational function. -/
theorem speedMuResidual810Scaled84_eq (h : F) (hh : h ≠ 0) (nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) :
    (17179869184 : F) * h ^ 84 *
        muResidual810
          (nL / 4)
          (nA / (16 * h ^ 14))
          (nB / (32 * h ^ 21))
          (nC / (2048 * h ^ 28))
          (nD / (1024 * h ^ 35))
          (nE / (65536 * h ^ 42))
          (nF / (131072 * h ^ 49))
          (nG / (16777216 * h ^ 56))
          (nP / (64 * h ^ 14))
          (nQ / (64 * h ^ 21))
          (nR / (2048 * h ^ 28))
          (nS / (8192 * h ^ 35))
          (nT / (131072 * h ^ 42))
          (nU / (262144 * h ^ 49))
          (nV / (16777216 * h ^ 56))
          (nW / (67108864 * h ^ 63)) =
      speedMuResidual810Scaled84 h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW := by
  have hd2 : (2 : F) ≠ 0 := by norm_num
  have hd4 : (4 : F) ≠ 0 := by norm_num
  have hd16 : (16 : F) ≠ 0 := by norm_num
  have hd32 : (32 : F) ≠ 0 := by norm_num
  have hd64 : (64 : F) ≠ 0 := by norm_num
  have hd1024 : (1024 : F) ≠ 0 := by norm_num
  have hd2048 : (2048 : F) ≠ 0 := by norm_num
  have hd8192 : (8192 : F) ≠ 0 := by norm_num
  have hd65536 : (65536 : F) ≠ 0 := by norm_num
  have hd131072 : (131072 : F) ≠ 0 := by norm_num
  have hd262144 : (262144 : F) ≠ 0 := by norm_num
  have hd16777216 : (16777216 : F) ≠ 0 := by norm_num
  have hd67108864 : (67108864 : F) ≠ 0 := by norm_num
  have hp14 : h ^ 14 ≠ 0 := pow_ne_zero 14 hh
  have hp21 : h ^ 21 ≠ 0 := pow_ne_zero 21 hh
  have hp28 : h ^ 28 ≠ 0 := pow_ne_zero 28 hh
  have hp35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hp42 : h ^ 42 ≠ 0 := pow_ne_zero 42 hh
  have hp49 : h ^ 49 ≠ 0 := pow_ne_zero 49 hh
  have hp56 : h ^ 56 ≠ 0 := pow_ne_zero 56 hh
  have hp63 : h ^ 63 ≠ 0 := pow_ne_zero 63 hh
  simp only [alphaResidual810, betaResidual810, deltaResidual810, epsilonResidual810, etaResidual810, gammaResidual810, muResidual810, zetaResidual810, speedMuResidual810Scaled84, fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk01, fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk02, fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk03, fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk04, fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk05, fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk06, fable810eleventhSpeedT_speedMuResidual810Scaled84_chunk07]
  field_simp
  ring


end Depression810TwelfthClearing

end Max11DegreeRoutes
end
