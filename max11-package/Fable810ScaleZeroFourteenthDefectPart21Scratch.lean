import Fable810ScaleZeroFourteenthDefectPart101Scratch
import Fable810ScaleZeroFourteenthDefectPart102Scratch

/-! Part 21 of 40 of `Fable810ScaleZeroFourteenthDefectScratch`, split so that no single module elaborates them all
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

section Depression810FifteenthClearing

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 64000000 in
private theorem astra4q_alpha810_homogeneous (t A P : F) :
    alphaResidual810 (t ^ 2 * A) (t ^ 2 * P) =
      t ^ 2 * alphaResidual810 A P := by
  simp only [alphaResidual810]
  ring

set_option maxHeartbeats 64000000 in
private theorem astra4q_beta810_homogeneous (t L A B Q : F) :
    betaResidual810 (t ^ 1 * L) (t ^ 2 * A) (t ^ 3 * B) (t ^ 3 * Q) =
      t ^ 3 * betaResidual810 L A B Q := by
  simp only [betaResidual810, astra4q_alpha810_homogeneous]
  ring

set_option maxHeartbeats 64000000 in
private theorem astra4q_gamma810_homogeneous (t L A B C0 P R : F) :
    gammaResidual810 (t ^ 1 * L) (t ^ 2 * A) (t ^ 3 * B) (t ^ 4 * C0) (t ^ 2 * P) (t ^ 4 * R) =
      t ^ 4 * gammaResidual810 L A B C0 P R := by
  simp only [gammaResidual810, astra4q_beta810_homogeneous, astra4q_alpha810_homogeneous]
  ring

set_option maxHeartbeats 64000000 in
private theorem astra4q_delta810_homogeneous (t L A B C0 D0 P Q S0 : F) :
    deltaResidual810 (t ^ 1 * L) (t ^ 2 * A) (t ^ 3 * B) (t ^ 4 * C0) (t ^ 5 * D0) (t ^ 2 * P) (t ^ 3 * Q) (t ^ 5 * S0) =
      t ^ 5 * deltaResidual810 L A B C0 D0 P Q S0 := by
  simp only [deltaResidual810, astra4q_gamma810_homogeneous, astra4q_beta810_homogeneous, astra4q_alpha810_homogeneous]
  ring

set_option maxHeartbeats 64000000 in
private theorem astra4q_epsilon810_homogeneous (t L A B C0 D0 E0 P Q R T0 : F) :
    epsilonResidual810 (t ^ 1 * L) (t ^ 2 * A) (t ^ 3 * B) (t ^ 4 * C0) (t ^ 5 * D0) (t ^ 6 * E0) (t ^ 2 * P) (t ^ 3 * Q) (t ^ 4 * R) (t ^ 6 * T0) =
      t ^ 6 * epsilonResidual810 L A B C0 D0 E0 P Q R T0 := by
  simp only [epsilonResidual810, astra4q_delta810_homogeneous, astra4q_gamma810_homogeneous, astra4q_beta810_homogeneous, astra4q_alpha810_homogeneous]
  ring

set_option maxHeartbeats 64000000 in
private theorem astra4q_zeta810_homogeneous (t L A B C0 D0 E0 F0 P Q R S0 U0 : F) :
    zetaResidual810 (t ^ 1 * L) (t ^ 2 * A) (t ^ 3 * B) (t ^ 4 * C0) (t ^ 5 * D0) (t ^ 6 * E0) (t ^ 7 * F0) (t ^ 2 * P) (t ^ 3 * Q) (t ^ 4 * R) (t ^ 5 * S0) (t ^ 7 * U0) =
      t ^ 7 * zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 := by
  simp only [zetaResidual810, astra4q_epsilon810_homogeneous, astra4q_delta810_homogeneous, astra4q_gamma810_homogeneous, astra4q_beta810_homogeneous, astra4q_alpha810_homogeneous]
  ring

set_option maxHeartbeats 64000000 in
private theorem astra4q_eta810_homogeneous (t L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 : F) :
    etaResidual810 (t ^ 1 * L) (t ^ 2 * A) (t ^ 3 * B) (t ^ 4 * C0) (t ^ 5 * D0) (t ^ 6 * E0) (t ^ 7 * F0) (t ^ 8 * G0) (t ^ 2 * P) (t ^ 3 * Q) (t ^ 4 * R) (t ^ 5 * S0) (t ^ 6 * T0) (t ^ 8 * V0) =
      t ^ 8 * etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 := by
  simp only [etaResidual810, astra4q_zeta810_homogeneous, astra4q_epsilon810_homogeneous, astra4q_delta810_homogeneous, astra4q_gamma810_homogeneous, astra4q_beta810_homogeneous, astra4q_alpha810_homogeneous]
  ring

set_option maxHeartbeats 64000000 in
private theorem astra4q_theta810_homogeneous (t L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 : F) :
    thetaResidual810 (t ^ 1 * L) (t ^ 2 * A) (t ^ 3 * B) (t ^ 4 * C0) (t ^ 5 * D0) (t ^ 6 * E0) (t ^ 7 * F0) (t ^ 8 * G0) (t ^ 2 * P) (t ^ 3 * Q) (t ^ 4 * R) (t ^ 5 * S0) (t ^ 6 * T0) (t ^ 7 * U0) (t ^ 9 * W0) =
      t ^ 9 * thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 := by
  simp only [thetaResidual810, astra4q_eta810_homogeneous, astra4q_zeta810_homogeneous, astra4q_epsilon810_homogeneous, astra4q_delta810_homogeneous, astra4q_gamma810_homogeneous, astra4q_beta810_homogeneous, astra4q_alpha810_homogeneous]
  ring

set_option maxHeartbeats 64000000 in
private theorem astra4q_omicron810_homogeneous (t L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 : F) :
    omicronResidual810 (t ^ 1 * L) (t ^ 2 * A) (t ^ 3 * B) (t ^ 4 * C0) (t ^ 5 * D0) (t ^ 6 * E0) (t ^ 7 * F0) (t ^ 8 * G0) (t ^ 2 * P) (t ^ 3 * Q) (t ^ 4 * R) (t ^ 5 * S0) (t ^ 6 * T0) (t ^ 7 * U0) (t ^ 8 * V0) (t ^ 9 * W0) =
      t ^ 15 * omicronResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 := by
  simp only [omicronResidual810, astra4q_theta810_homogeneous, astra4q_eta810_homogeneous, astra4q_zeta810_homogeneous, astra4q_epsilon810_homogeneous, astra4q_delta810_homogeneous, astra4q_gamma810_homogeneous, astra4q_beta810_homogeneous, astra4q_alpha810_homogeneous]
  ring

set_option maxHeartbeats 64000000 in
private theorem astra4q_omicron810_cancel (h : F) (hh : h ≠ 0)
    (k : ℕ) (n d : F) :
    (h ^ 7) ^ k * (n / (d * h ^ (7 * k))) = n / d := by
  rw [← pow_mul]
  by_cases hd : d = 0
  · simp [hd]
  · field_simp [hh] <;> ring

set_option maxHeartbeats 64000000 in
/-- Only numeric denominators remain in the polynomial expansion certificate. -/
private theorem astra4q_omicron810_numeric (h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) :
    (36028797018963968 : F) * omicronResidual810
      (h ^ 7 * (nL / 4))
      (nA / 16)
      (nB / 32)
      (nC / 2048)
      (nD / 1024)
      (nE / 65536)
      (nF / 131072)
      (nG / 16777216)
      (nP / 64)
      (nQ / 64)
      (nR / 2048)
      (nS / 8192)
      (nT / 131072)
      (nU / 262144)
      (nV / 16777216)
      (nW / 67108864) =
      speedOmicronScaled810 h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW := by
  simp only [omicronResidual810, thetaResidual810, etaResidual810,
    zetaResidual810, epsilonResidual810, deltaResidual810, gammaResidual810,
    betaResidual810, alphaResidual810, speedOmicronScaled810]
  ring


set_option maxHeartbeats 64000000 in
/-- The atom-level clearing.  One `field_simp` over 17 atomic variables, in
place of the single enormous `field_simp` on the fully substituted rational
function.  This is the whole of recipe R2. -/
theorem speedOmicronScaled810_eq (h : F) (hh : h ≠ 0)
    (nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW : F) :
    (36028797018963968 : F) * h ^ 105 *
        omicronResidual810
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
      speedOmicronScaled810 h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW := by
  -- Peel weighted scaling before expanding the residual tower.
  have hs := astra4q_omicron810_homogeneous (h ^ 7)
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
    (nW / (67108864 * h ^ 63))
  simp only [astra4q_omicron810_cancel h hh, pow_one] at hs
  have hp : (h ^ 7) ^ 15 = h ^ 105 := by rw [← pow_mul]
  rw [hp] at hs
  calc
    _ = (36028797018963968 : F) *
        (h ^ 105 * omicronResidual810
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
          (nW / (67108864 * h ^ 63))) := mul_assoc _ _ _
    _ = _ := congrArg (fun z : F => (36028797018963968 : F) * z) hs.symm
    _ = _ := astra4q_omicron810_numeric h nL nA nB nC nD nE nF nG nP nQ nR nS nT nU nV nW



end Depression810FifteenthClearing
end Max11DegreeRoutes
end
