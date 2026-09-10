import Fable810ScaleZeroThirteenthDefectPart17Scratch

/-! Part 18 of 37 of `Fable810ScaleZeroThirteenthDefectScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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

section Depression810FourteenthClearing

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 400000000 in
/-- The atom-level clearing: one `field_simp` over 17 atomic variables in
place of the single enormous `field_simp` on the substituted rational function. -/
theorem speedXiResidual810Scaled98_eq (h : F) (hh : h ≠ 0) (nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) :
    (8796093022208 : F) * h ^ 98 *
        xiResidual810
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
      speedXiResidual810Scaled98 h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW := by
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
  simp only [alphaResidual810, betaResidual810, deltaResidual810, epsilonResidual810, etaResidual810, gammaResidual810, thetaResidual810, xiResidual810, zetaResidual810, speedXiResidual810Scaled98]
  field_simp
  ring


end Depression810FourteenthClearing
end Max11DegreeRoutes
end
