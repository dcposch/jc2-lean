import Grok810ScaleZeroQuarticFullConeD6F6Part25Scratch
import Grok810ScaleZeroQuarticFullConeD6F6Part26Scratch
import Grok810ScaleZeroQuarticFullConeD6F6Part58Scratch

/-! Part 59 of 61 of `Grok810ScaleZeroQuarticFullConeD6F6Scratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

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
set_option maxHeartbeats 64000000

section QuarticFullConeABCDEFG810D6F6

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000


set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6P9_eq_viaf
    (b c d f : k) :
    quarticCoreD6F6A9ABCDEFG810 b c d f * quarticCoreResE_U22_U25bABCDEFG810 b c d f =
      quarticCoreD6F6P9viaABCDEFG810 b c d f := by
  rw [quarticCoreD6F6A9_cfsplit, quarticCoreD6F6E9_cfsplit]
  rw [quarticCoreD6F6P9viaABCDEFG810]
  rw [← quarticCoreD6F6P9c0f1_from, ← quarticCoreD6F6P9c0f2_from, ← quarticCoreD6F6P9c0f3_from, ← quarticCoreD6F6P9c0f4_from, ← quarticCoreD6F6P9c0f5_from, ← quarticCoreD6F6P9c0f6_from, ← quarticCoreD6F6P9c0f7_from, ← quarticCoreD6F6P9c0f8_from, ← quarticCoreD6F6P9c1f0_from, ← quarticCoreD6F6P9c1f1_from, ← quarticCoreD6F6P9c1f2_from, ← quarticCoreD6F6P9c1f3_from, ← quarticCoreD6F6P9c1f4_from, ← quarticCoreD6F6P9c1f5_from, ← quarticCoreD6F6P9c1f6_from, ← quarticCoreD6F6P9c1f7_from, ← quarticCoreD6F6P9c1f8_from, ← quarticCoreD6F6P9c2f0_from, ← quarticCoreD6F6P9c2f1_from, ← quarticCoreD6F6P9c2f2_from, ← quarticCoreD6F6P9c2f3_from, ← quarticCoreD6F6P9c2f4_from, ← quarticCoreD6F6P9c2f5_from, ← quarticCoreD6F6P9c2f6_from, ← quarticCoreD6F6P9c2f7_from, ← quarticCoreD6F6P9c3f0_from, ← quarticCoreD6F6P9c3f1_from, ← quarticCoreD6F6P9c3f2_from, ← quarticCoreD6F6P9c3f3_from, ← quarticCoreD6F6P9c3f4_from, ← quarticCoreD6F6P9c3f5_from, ← quarticCoreD6F6P9c3f6_from, ← quarticCoreD6F6P9c4f0_from, ← quarticCoreD6F6P9c4f1_from, ← quarticCoreD6F6P9c4f2_from, ← quarticCoreD6F6P9c4f3_from, ← quarticCoreD6F6P9c4f4_from, ← quarticCoreD6F6P9c4f5_from, ← quarticCoreD6F6P9c4f6_from, ← quarticCoreD6F6P9c5f0_from, ← quarticCoreD6F6P9c5f1_from, ← quarticCoreD6F6P9c5f2_from, ← quarticCoreD6F6P9c5f3_from, ← quarticCoreD6F6P9c5f4_from, ← quarticCoreD6F6P9c5f5_from, ← quarticCoreD6F6P9c6f0_from, ← quarticCoreD6F6P9c6f1_from, ← quarticCoreD6F6P9c6f2_from, ← quarticCoreD6F6P9c6f3_from, ← quarticCoreD6F6P9c6f4_from, ← quarticCoreD6F6P9c7f0_from, ← quarticCoreD6F6P9c7f1_from, ← quarticCoreD6F6P9c7f2_from, ← quarticCoreD6F6P9c7f3_from, ← quarticCoreD6F6P9c8f0_from, ← quarticCoreD6F6P9c8f1_from, ← quarticCoreD6F6P9c8f2_from, ← quarticCoreD6F6P9c9f0_from, ← quarticCoreD6F6P9c9f1_from, ← quarticCoreD6F6P9c10f0_from]
  generalize hA9c0f0 : quarticCoreD6F6A9c0f0ABCDEFG810 b d = xA9c0f0
  generalize hA9c0f1 : quarticCoreD6F6A9c0f1ABCDEFG810 b d = xA9c0f1
  generalize hA9c0f2 : quarticCoreD6F6A9c0f2ABCDEFG810 b d = xA9c0f2
  generalize hA9c0f3 : quarticCoreD6F6A9c0f3ABCDEFG810 b d = xA9c0f3
  generalize hA9c1f0 : quarticCoreD6F6A9c1f0ABCDEFG810 b d = xA9c1f0
  generalize hA9c1f1 : quarticCoreD6F6A9c1f1ABCDEFG810 b d = xA9c1f1
  generalize hA9c1f2 : quarticCoreD6F6A9c1f2ABCDEFG810 b d = xA9c1f2
  generalize hA9c2f0 : quarticCoreD6F6A9c2f0ABCDEFG810 b d = xA9c2f0
  generalize hA9c2f1 : quarticCoreD6F6A9c2f1ABCDEFG810 b d = xA9c2f1
  generalize hA9c3f0 : quarticCoreD6F6A9c3f0ABCDEFG810 b d = xA9c3f0
  generalize hA9c3f1 : quarticCoreD6F6A9c3f1ABCDEFG810 b d = xA9c3f1
  generalize hA9c4f0 : quarticCoreD6F6A9c4f0ABCDEFG810 b d = xA9c4f0
  generalize hE9c0f1 : quarticCoreD6F6E9c0f1ABCDEFG810 b d = xE9c0f1
  generalize hE9c0f2 : quarticCoreD6F6E9c0f2ABCDEFG810 b d = xE9c0f2
  generalize hE9c0f3 : quarticCoreD6F6E9c0f3ABCDEFG810 b d = xE9c0f3
  generalize hE9c0f4 : quarticCoreD6F6E9c0f4ABCDEFG810 b d = xE9c0f4
  generalize hE9c0f5 : quarticCoreD6F6E9c0f5ABCDEFG810 b d = xE9c0f5
  generalize hE9c1f0 : quarticCoreD6F6E9c1f0ABCDEFG810 b d = xE9c1f0
  generalize hE9c1f1 : quarticCoreD6F6E9c1f1ABCDEFG810 b d = xE9c1f1
  generalize hE9c1f2 : quarticCoreD6F6E9c1f2ABCDEFG810 b d = xE9c1f2
  generalize hE9c1f3 : quarticCoreD6F6E9c1f3ABCDEFG810 b d = xE9c1f3
  generalize hE9c1f4 : quarticCoreD6F6E9c1f4ABCDEFG810 b d = xE9c1f4
  generalize hE9c1f5 : quarticCoreD6F6E9c1f5ABCDEFG810 b d = xE9c1f5
  generalize hE9c2f0 : quarticCoreD6F6E9c2f0ABCDEFG810 b d = xE9c2f0
  generalize hE9c2f1 : quarticCoreD6F6E9c2f1ABCDEFG810 b d = xE9c2f1
  generalize hE9c2f2 : quarticCoreD6F6E9c2f2ABCDEFG810 b d = xE9c2f2
  generalize hE9c2f3 : quarticCoreD6F6E9c2f3ABCDEFG810 b d = xE9c2f3
  generalize hE9c2f4 : quarticCoreD6F6E9c2f4ABCDEFG810 b d = xE9c2f4
  generalize hE9c3f0 : quarticCoreD6F6E9c3f0ABCDEFG810 b d = xE9c3f0
  generalize hE9c3f1 : quarticCoreD6F6E9c3f1ABCDEFG810 b d = xE9c3f1
  generalize hE9c3f2 : quarticCoreD6F6E9c3f2ABCDEFG810 b d = xE9c3f2
  generalize hE9c3f3 : quarticCoreD6F6E9c3f3ABCDEFG810 b d = xE9c3f3
  generalize hE9c4f0 : quarticCoreD6F6E9c4f0ABCDEFG810 b d = xE9c4f0
  generalize hE9c4f1 : quarticCoreD6F6E9c4f1ABCDEFG810 b d = xE9c4f1
  generalize hE9c4f2 : quarticCoreD6F6E9c4f2ABCDEFG810 b d = xE9c4f2
  generalize hE9c5f0 : quarticCoreD6F6E9c5f0ABCDEFG810 b d = xE9c5f0
  generalize hE9c5f1 : quarticCoreD6F6E9c5f1ABCDEFG810 b d = xE9c5f1
  generalize hE9c6f0 : quarticCoreD6F6E9c6f0ABCDEFG810 b d = xE9c6f0
  try ring

/-! ## Bidegree combination `Σ_i P_i = N d^6` at `(c, f) = (0, 6)` -/
set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c0f0
    (b d : k) :
    quarticCoreD6F6P1c0f0ABCDEFG810 b d +
        quarticCoreD6F6P2c0f0ABCDEFG810 b d +
        quarticCoreD6F6P3c0f0ABCDEFG810 b d +
        quarticCoreD6F6P5c0f0ABCDEFG810 b d +
        quarticCoreD6F6P6c0f0ABCDEFG810 b d +
        quarticCoreD6F6P7c0f0ABCDEFG810 b d +
        quarticCoreD6F6P8c0f0ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c0f0ABCDEFG810, quarticCoreD6F6P2c0f0ABCDEFG810, quarticCoreD6F6P3c0f0ABCDEFG810, quarticCoreD6F6P5c0f0ABCDEFG810, quarticCoreD6F6P6c0f0ABCDEFG810, quarticCoreD6F6P7c0f0ABCDEFG810, quarticCoreD6F6P8c0f0ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c0f1
    (b d : k) :
    quarticCoreD6F6P1c0f1ABCDEFG810 b d +
        quarticCoreD6F6P2c0f1ABCDEFG810 b d +
        quarticCoreD6F6P3c0f1ABCDEFG810 b d +
        quarticCoreD6F6P4c0f1ABCDEFG810 b d +
        quarticCoreD6F6P5c0f1ABCDEFG810 b d +
        quarticCoreD6F6P6c0f1ABCDEFG810 b d +
        quarticCoreD6F6P7c0f1ABCDEFG810 b d +
        quarticCoreD6F6P8c0f1ABCDEFG810 b d +
        quarticCoreD6F6P9c0f1ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c0f1ABCDEFG810, quarticCoreD6F6P2c0f1ABCDEFG810, quarticCoreD6F6P3c0f1ABCDEFG810, quarticCoreD6F6P4c0f1ABCDEFG810, quarticCoreD6F6P5c0f1ABCDEFG810, quarticCoreD6F6P6c0f1ABCDEFG810, quarticCoreD6F6P7c0f1ABCDEFG810, quarticCoreD6F6P8c0f1ABCDEFG810, quarticCoreD6F6P9c0f1ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c0f2
    (b d : k) :
    quarticCoreD6F6P1c0f2ABCDEFG810 b d +
        quarticCoreD6F6P2c0f2ABCDEFG810 b d +
        quarticCoreD6F6P3c0f2ABCDEFG810 b d +
        quarticCoreD6F6P4c0f2ABCDEFG810 b d +
        quarticCoreD6F6P5c0f2ABCDEFG810 b d +
        quarticCoreD6F6P6c0f2ABCDEFG810 b d +
        quarticCoreD6F6P7c0f2ABCDEFG810 b d +
        quarticCoreD6F6P8c0f2ABCDEFG810 b d +
        quarticCoreD6F6P9c0f2ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c0f2ABCDEFG810, quarticCoreD6F6P2c0f2ABCDEFG810, quarticCoreD6F6P3c0f2ABCDEFG810, quarticCoreD6F6P4c0f2ABCDEFG810, quarticCoreD6F6P5c0f2ABCDEFG810, quarticCoreD6F6P6c0f2ABCDEFG810, quarticCoreD6F6P7c0f2ABCDEFG810, quarticCoreD6F6P8c0f2ABCDEFG810, quarticCoreD6F6P9c0f2ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c0f3
    (b d : k) :
    quarticCoreD6F6P1c0f3ABCDEFG810 b d +
        quarticCoreD6F6P2c0f3ABCDEFG810 b d +
        quarticCoreD6F6P3c0f3ABCDEFG810 b d +
        quarticCoreD6F6P4c0f3ABCDEFG810 b d +
        quarticCoreD6F6P5c0f3ABCDEFG810 b d +
        quarticCoreD6F6P6c0f3ABCDEFG810 b d +
        quarticCoreD6F6P7c0f3ABCDEFG810 b d +
        quarticCoreD6F6P8c0f3ABCDEFG810 b d +
        quarticCoreD6F6P9c0f3ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c0f3ABCDEFG810, quarticCoreD6F6P2c0f3ABCDEFG810, quarticCoreD6F6P3c0f3ABCDEFG810, quarticCoreD6F6P4c0f3ABCDEFG810, quarticCoreD6F6P5c0f3ABCDEFG810, quarticCoreD6F6P6c0f3ABCDEFG810, quarticCoreD6F6P7c0f3ABCDEFG810, quarticCoreD6F6P8c0f3ABCDEFG810, quarticCoreD6F6P9c0f3ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c0f4
    (b d : k) :
    quarticCoreD6F6P1c0f4ABCDEFG810 b d +
        quarticCoreD6F6P2c0f4ABCDEFG810 b d +
        quarticCoreD6F6P3c0f4ABCDEFG810 b d +
        quarticCoreD6F6P4c0f4ABCDEFG810 b d +
        quarticCoreD6F6P5c0f4ABCDEFG810 b d +
        quarticCoreD6F6P6c0f4ABCDEFG810 b d +
        quarticCoreD6F6P7c0f4ABCDEFG810 b d +
        quarticCoreD6F6P8c0f4ABCDEFG810 b d +
        quarticCoreD6F6P9c0f4ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c0f4ABCDEFG810, quarticCoreD6F6P2c0f4ABCDEFG810, quarticCoreD6F6P3c0f4ABCDEFG810, quarticCoreD6F6P4c0f4ABCDEFG810, quarticCoreD6F6P5c0f4ABCDEFG810, quarticCoreD6F6P6c0f4ABCDEFG810, quarticCoreD6F6P7c0f4ABCDEFG810, quarticCoreD6F6P8c0f4ABCDEFG810, quarticCoreD6F6P9c0f4ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c0f5
    (b d : k) :
    quarticCoreD6F6P1c0f5ABCDEFG810 b d +
        quarticCoreD6F6P2c0f5ABCDEFG810 b d +
        quarticCoreD6F6P3c0f5ABCDEFG810 b d +
        quarticCoreD6F6P4c0f5ABCDEFG810 b d +
        quarticCoreD6F6P5c0f5ABCDEFG810 b d +
        quarticCoreD6F6P6c0f5ABCDEFG810 b d +
        quarticCoreD6F6P7c0f5ABCDEFG810 b d +
        quarticCoreD6F6P8c0f5ABCDEFG810 b d +
        quarticCoreD6F6P9c0f5ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c0f5ABCDEFG810, quarticCoreD6F6P2c0f5ABCDEFG810, quarticCoreD6F6P3c0f5ABCDEFG810, quarticCoreD6F6P4c0f5ABCDEFG810, quarticCoreD6F6P5c0f5ABCDEFG810, quarticCoreD6F6P6c0f5ABCDEFG810, quarticCoreD6F6P7c0f5ABCDEFG810, quarticCoreD6F6P8c0f5ABCDEFG810, quarticCoreD6F6P9c0f5ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c0f6
    (b d : k) :
    quarticCoreD6F6P1c0f6ABCDEFG810 b d +
        quarticCoreD6F6P2c0f6ABCDEFG810 b d +
        quarticCoreD6F6P3c0f6ABCDEFG810 b d +
        quarticCoreD6F6P4c0f6ABCDEFG810 b d +
        quarticCoreD6F6P5c0f6ABCDEFG810 b d +
        quarticCoreD6F6P6c0f6ABCDEFG810 b d +
        quarticCoreD6F6P7c0f6ABCDEFG810 b d +
        quarticCoreD6F6P8c0f6ABCDEFG810 b d +
        quarticCoreD6F6P9c0f6ABCDEFG810 b d =
      (quarticCoreD6F6NABCDEFG810 : k) * d ^ 6 := by
  simp only [quarticCoreD6F6P1c0f6ABCDEFG810, quarticCoreD6F6P2c0f6ABCDEFG810, quarticCoreD6F6P3c0f6ABCDEFG810, quarticCoreD6F6P4c0f6ABCDEFG810, quarticCoreD6F6P5c0f6ABCDEFG810, quarticCoreD6F6P6c0f6ABCDEFG810, quarticCoreD6F6P7c0f6ABCDEFG810, quarticCoreD6F6P8c0f6ABCDEFG810, quarticCoreD6F6P9c0f6ABCDEFG810, quarticCoreD6F6NABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c0f7
    (b d : k) :
    quarticCoreD6F6P1c0f7ABCDEFG810 b d +
        quarticCoreD6F6P2c0f7ABCDEFG810 b d +
        quarticCoreD6F6P3c0f7ABCDEFG810 b d +
        quarticCoreD6F6P4c0f7ABCDEFG810 b d +
        quarticCoreD6F6P5c0f7ABCDEFG810 b d +
        quarticCoreD6F6P6c0f7ABCDEFG810 b d +
        quarticCoreD6F6P7c0f7ABCDEFG810 b d +
        quarticCoreD6F6P9c0f7ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c0f7ABCDEFG810, quarticCoreD6F6P2c0f7ABCDEFG810, quarticCoreD6F6P3c0f7ABCDEFG810, quarticCoreD6F6P4c0f7ABCDEFG810, quarticCoreD6F6P5c0f7ABCDEFG810, quarticCoreD6F6P6c0f7ABCDEFG810, quarticCoreD6F6P7c0f7ABCDEFG810, quarticCoreD6F6P9c0f7ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c0f8
    (b d : k) :
    quarticCoreD6F6P1c0f8ABCDEFG810 b d +
        quarticCoreD6F6P2c0f8ABCDEFG810 b d +
        quarticCoreD6F6P3c0f8ABCDEFG810 b d +
        quarticCoreD6F6P4c0f8ABCDEFG810 b d +
        quarticCoreD6F6P5c0f8ABCDEFG810 b d +
        quarticCoreD6F6P6c0f8ABCDEFG810 b d +
        quarticCoreD6F6P9c0f8ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c0f8ABCDEFG810, quarticCoreD6F6P2c0f8ABCDEFG810, quarticCoreD6F6P3c0f8ABCDEFG810, quarticCoreD6F6P4c0f8ABCDEFG810, quarticCoreD6F6P5c0f8ABCDEFG810, quarticCoreD6F6P6c0f8ABCDEFG810, quarticCoreD6F6P9c0f8ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c1f0
    (b d : k) :
    quarticCoreD6F6P1c1f0ABCDEFG810 b d +
        quarticCoreD6F6P2c1f0ABCDEFG810 b d +
        quarticCoreD6F6P3c1f0ABCDEFG810 b d +
        quarticCoreD6F6P4c1f0ABCDEFG810 b d +
        quarticCoreD6F6P5c1f0ABCDEFG810 b d +
        quarticCoreD6F6P6c1f0ABCDEFG810 b d +
        quarticCoreD6F6P7c1f0ABCDEFG810 b d +
        quarticCoreD6F6P8c1f0ABCDEFG810 b d +
        quarticCoreD6F6P9c1f0ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c1f0ABCDEFG810, quarticCoreD6F6P2c1f0ABCDEFG810, quarticCoreD6F6P3c1f0ABCDEFG810, quarticCoreD6F6P4c1f0ABCDEFG810, quarticCoreD6F6P5c1f0ABCDEFG810, quarticCoreD6F6P6c1f0ABCDEFG810, quarticCoreD6F6P7c1f0ABCDEFG810, quarticCoreD6F6P8c1f0ABCDEFG810, quarticCoreD6F6P9c1f0ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c1f1
    (b d : k) :
    quarticCoreD6F6P1c1f1ABCDEFG810 b d +
        quarticCoreD6F6P2c1f1ABCDEFG810 b d +
        quarticCoreD6F6P3c1f1ABCDEFG810 b d +
        quarticCoreD6F6P4c1f1ABCDEFG810 b d +
        quarticCoreD6F6P5c1f1ABCDEFG810 b d +
        quarticCoreD6F6P6c1f1ABCDEFG810 b d +
        quarticCoreD6F6P7c1f1ABCDEFG810 b d +
        quarticCoreD6F6P8c1f1ABCDEFG810 b d +
        quarticCoreD6F6P9c1f1ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c1f1ABCDEFG810, quarticCoreD6F6P2c1f1ABCDEFG810, quarticCoreD6F6P3c1f1ABCDEFG810, quarticCoreD6F6P4c1f1ABCDEFG810, quarticCoreD6F6P5c1f1ABCDEFG810, quarticCoreD6F6P6c1f1ABCDEFG810, quarticCoreD6F6P7c1f1ABCDEFG810, quarticCoreD6F6P8c1f1ABCDEFG810, quarticCoreD6F6P9c1f1ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c1f2
    (b d : k) :
    quarticCoreD6F6P1c1f2ABCDEFG810 b d +
        quarticCoreD6F6P2c1f2ABCDEFG810 b d +
        quarticCoreD6F6P3c1f2ABCDEFG810 b d +
        quarticCoreD6F6P4c1f2ABCDEFG810 b d +
        quarticCoreD6F6P5c1f2ABCDEFG810 b d +
        quarticCoreD6F6P6c1f2ABCDEFG810 b d +
        quarticCoreD6F6P7c1f2ABCDEFG810 b d +
        quarticCoreD6F6P8c1f2ABCDEFG810 b d +
        quarticCoreD6F6P9c1f2ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c1f2ABCDEFG810, quarticCoreD6F6P2c1f2ABCDEFG810, quarticCoreD6F6P3c1f2ABCDEFG810, quarticCoreD6F6P4c1f2ABCDEFG810, quarticCoreD6F6P5c1f2ABCDEFG810, quarticCoreD6F6P6c1f2ABCDEFG810, quarticCoreD6F6P7c1f2ABCDEFG810, quarticCoreD6F6P8c1f2ABCDEFG810, quarticCoreD6F6P9c1f2ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c1f3
    (b d : k) :
    quarticCoreD6F6P1c1f3ABCDEFG810 b d +
        quarticCoreD6F6P2c1f3ABCDEFG810 b d +
        quarticCoreD6F6P3c1f3ABCDEFG810 b d +
        quarticCoreD6F6P4c1f3ABCDEFG810 b d +
        quarticCoreD6F6P5c1f3ABCDEFG810 b d +
        quarticCoreD6F6P6c1f3ABCDEFG810 b d +
        quarticCoreD6F6P7c1f3ABCDEFG810 b d +
        quarticCoreD6F6P8c1f3ABCDEFG810 b d +
        quarticCoreD6F6P9c1f3ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c1f3ABCDEFG810, quarticCoreD6F6P2c1f3ABCDEFG810, quarticCoreD6F6P3c1f3ABCDEFG810, quarticCoreD6F6P4c1f3ABCDEFG810, quarticCoreD6F6P5c1f3ABCDEFG810, quarticCoreD6F6P6c1f3ABCDEFG810, quarticCoreD6F6P7c1f3ABCDEFG810, quarticCoreD6F6P8c1f3ABCDEFG810, quarticCoreD6F6P9c1f3ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c1f4
    (b d : k) :
    quarticCoreD6F6P1c1f4ABCDEFG810 b d +
        quarticCoreD6F6P2c1f4ABCDEFG810 b d +
        quarticCoreD6F6P3c1f4ABCDEFG810 b d +
        quarticCoreD6F6P4c1f4ABCDEFG810 b d +
        quarticCoreD6F6P5c1f4ABCDEFG810 b d +
        quarticCoreD6F6P6c1f4ABCDEFG810 b d +
        quarticCoreD6F6P7c1f4ABCDEFG810 b d +
        quarticCoreD6F6P8c1f4ABCDEFG810 b d +
        quarticCoreD6F6P9c1f4ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c1f4ABCDEFG810, quarticCoreD6F6P2c1f4ABCDEFG810, quarticCoreD6F6P3c1f4ABCDEFG810, quarticCoreD6F6P4c1f4ABCDEFG810, quarticCoreD6F6P5c1f4ABCDEFG810, quarticCoreD6F6P6c1f4ABCDEFG810, quarticCoreD6F6P7c1f4ABCDEFG810, quarticCoreD6F6P8c1f4ABCDEFG810, quarticCoreD6F6P9c1f4ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c1f5
    (b d : k) :
    quarticCoreD6F6P1c1f5ABCDEFG810 b d +
        quarticCoreD6F6P2c1f5ABCDEFG810 b d +
        quarticCoreD6F6P3c1f5ABCDEFG810 b d +
        quarticCoreD6F6P4c1f5ABCDEFG810 b d +
        quarticCoreD6F6P5c1f5ABCDEFG810 b d +
        quarticCoreD6F6P6c1f5ABCDEFG810 b d +
        quarticCoreD6F6P7c1f5ABCDEFG810 b d +
        quarticCoreD6F6P8c1f5ABCDEFG810 b d +
        quarticCoreD6F6P9c1f5ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c1f5ABCDEFG810, quarticCoreD6F6P2c1f5ABCDEFG810, quarticCoreD6F6P3c1f5ABCDEFG810, quarticCoreD6F6P4c1f5ABCDEFG810, quarticCoreD6F6P5c1f5ABCDEFG810, quarticCoreD6F6P6c1f5ABCDEFG810, quarticCoreD6F6P7c1f5ABCDEFG810, quarticCoreD6F6P8c1f5ABCDEFG810, quarticCoreD6F6P9c1f5ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c1f6
    (b d : k) :
    quarticCoreD6F6P1c1f6ABCDEFG810 b d +
        quarticCoreD6F6P2c1f6ABCDEFG810 b d +
        quarticCoreD6F6P3c1f6ABCDEFG810 b d +
        quarticCoreD6F6P4c1f6ABCDEFG810 b d +
        quarticCoreD6F6P5c1f6ABCDEFG810 b d +
        quarticCoreD6F6P6c1f6ABCDEFG810 b d +
        quarticCoreD6F6P7c1f6ABCDEFG810 b d +
        quarticCoreD6F6P8c1f6ABCDEFG810 b d +
        quarticCoreD6F6P9c1f6ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c1f6ABCDEFG810, quarticCoreD6F6P2c1f6ABCDEFG810, quarticCoreD6F6P3c1f6ABCDEFG810, quarticCoreD6F6P4c1f6ABCDEFG810, quarticCoreD6F6P5c1f6ABCDEFG810, quarticCoreD6F6P6c1f6ABCDEFG810, quarticCoreD6F6P7c1f6ABCDEFG810, quarticCoreD6F6P8c1f6ABCDEFG810, quarticCoreD6F6P9c1f6ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c1f7
    (b d : k) :
    quarticCoreD6F6P1c1f7ABCDEFG810 b d +
        quarticCoreD6F6P2c1f7ABCDEFG810 b d +
        quarticCoreD6F6P3c1f7ABCDEFG810 b d +
        quarticCoreD6F6P4c1f7ABCDEFG810 b d +
        quarticCoreD6F6P5c1f7ABCDEFG810 b d +
        quarticCoreD6F6P6c1f7ABCDEFG810 b d +
        quarticCoreD6F6P7c1f7ABCDEFG810 b d +
        quarticCoreD6F6P8c1f7ABCDEFG810 b d +
        quarticCoreD6F6P9c1f7ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c1f7ABCDEFG810, quarticCoreD6F6P2c1f7ABCDEFG810, quarticCoreD6F6P3c1f7ABCDEFG810, quarticCoreD6F6P4c1f7ABCDEFG810, quarticCoreD6F6P5c1f7ABCDEFG810, quarticCoreD6F6P6c1f7ABCDEFG810, quarticCoreD6F6P7c1f7ABCDEFG810, quarticCoreD6F6P8c1f7ABCDEFG810, quarticCoreD6F6P9c1f7ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c1f8
    (b d : k) :
    quarticCoreD6F6P4c1f8ABCDEFG810 b d +
        quarticCoreD6F6P5c1f8ABCDEFG810 b d +
        quarticCoreD6F6P6c1f8ABCDEFG810 b d +
        quarticCoreD6F6P7c1f8ABCDEFG810 b d +
        quarticCoreD6F6P9c1f8ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P4c1f8ABCDEFG810, quarticCoreD6F6P5c1f8ABCDEFG810, quarticCoreD6F6P6c1f8ABCDEFG810, quarticCoreD6F6P7c1f8ABCDEFG810, quarticCoreD6F6P9c1f8ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c2f0
    (b d : k) :
    quarticCoreD6F6P1c2f0ABCDEFG810 b d +
        quarticCoreD6F6P2c2f0ABCDEFG810 b d +
        quarticCoreD6F6P3c2f0ABCDEFG810 b d +
        quarticCoreD6F6P4c2f0ABCDEFG810 b d +
        quarticCoreD6F6P5c2f0ABCDEFG810 b d +
        quarticCoreD6F6P6c2f0ABCDEFG810 b d +
        quarticCoreD6F6P7c2f0ABCDEFG810 b d +
        quarticCoreD6F6P8c2f0ABCDEFG810 b d +
        quarticCoreD6F6P9c2f0ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c2f0ABCDEFG810, quarticCoreD6F6P2c2f0ABCDEFG810, quarticCoreD6F6P3c2f0ABCDEFG810, quarticCoreD6F6P4c2f0ABCDEFG810, quarticCoreD6F6P5c2f0ABCDEFG810, quarticCoreD6F6P6c2f0ABCDEFG810, quarticCoreD6F6P7c2f0ABCDEFG810, quarticCoreD6F6P8c2f0ABCDEFG810, quarticCoreD6F6P9c2f0ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c2f1
    (b d : k) :
    quarticCoreD6F6P1c2f1ABCDEFG810 b d +
        quarticCoreD6F6P2c2f1ABCDEFG810 b d +
        quarticCoreD6F6P3c2f1ABCDEFG810 b d +
        quarticCoreD6F6P4c2f1ABCDEFG810 b d +
        quarticCoreD6F6P5c2f1ABCDEFG810 b d +
        quarticCoreD6F6P6c2f1ABCDEFG810 b d +
        quarticCoreD6F6P7c2f1ABCDEFG810 b d +
        quarticCoreD6F6P8c2f1ABCDEFG810 b d +
        quarticCoreD6F6P9c2f1ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c2f1ABCDEFG810, quarticCoreD6F6P2c2f1ABCDEFG810, quarticCoreD6F6P3c2f1ABCDEFG810, quarticCoreD6F6P4c2f1ABCDEFG810, quarticCoreD6F6P5c2f1ABCDEFG810, quarticCoreD6F6P6c2f1ABCDEFG810, quarticCoreD6F6P7c2f1ABCDEFG810, quarticCoreD6F6P8c2f1ABCDEFG810, quarticCoreD6F6P9c2f1ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c2f2
    (b d : k) :
    quarticCoreD6F6P1c2f2ABCDEFG810 b d +
        quarticCoreD6F6P2c2f2ABCDEFG810 b d +
        quarticCoreD6F6P3c2f2ABCDEFG810 b d +
        quarticCoreD6F6P4c2f2ABCDEFG810 b d +
        quarticCoreD6F6P5c2f2ABCDEFG810 b d +
        quarticCoreD6F6P6c2f2ABCDEFG810 b d +
        quarticCoreD6F6P7c2f2ABCDEFG810 b d +
        quarticCoreD6F6P8c2f2ABCDEFG810 b d +
        quarticCoreD6F6P9c2f2ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c2f2ABCDEFG810, quarticCoreD6F6P2c2f2ABCDEFG810, quarticCoreD6F6P3c2f2ABCDEFG810, quarticCoreD6F6P4c2f2ABCDEFG810, quarticCoreD6F6P5c2f2ABCDEFG810, quarticCoreD6F6P6c2f2ABCDEFG810, quarticCoreD6F6P7c2f2ABCDEFG810, quarticCoreD6F6P8c2f2ABCDEFG810, quarticCoreD6F6P9c2f2ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c2f3
    (b d : k) :
    quarticCoreD6F6P1c2f3ABCDEFG810 b d +
        quarticCoreD6F6P2c2f3ABCDEFG810 b d +
        quarticCoreD6F6P3c2f3ABCDEFG810 b d +
        quarticCoreD6F6P4c2f3ABCDEFG810 b d +
        quarticCoreD6F6P5c2f3ABCDEFG810 b d +
        quarticCoreD6F6P6c2f3ABCDEFG810 b d +
        quarticCoreD6F6P7c2f3ABCDEFG810 b d +
        quarticCoreD6F6P8c2f3ABCDEFG810 b d +
        quarticCoreD6F6P9c2f3ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c2f3ABCDEFG810, quarticCoreD6F6P2c2f3ABCDEFG810, quarticCoreD6F6P3c2f3ABCDEFG810, quarticCoreD6F6P4c2f3ABCDEFG810, quarticCoreD6F6P5c2f3ABCDEFG810, quarticCoreD6F6P6c2f3ABCDEFG810, quarticCoreD6F6P7c2f3ABCDEFG810, quarticCoreD6F6P8c2f3ABCDEFG810, quarticCoreD6F6P9c2f3ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c2f4
    (b d : k) :
    quarticCoreD6F6P1c2f4ABCDEFG810 b d +
        quarticCoreD6F6P2c2f4ABCDEFG810 b d +
        quarticCoreD6F6P3c2f4ABCDEFG810 b d +
        quarticCoreD6F6P4c2f4ABCDEFG810 b d +
        quarticCoreD6F6P5c2f4ABCDEFG810 b d +
        quarticCoreD6F6P6c2f4ABCDEFG810 b d +
        quarticCoreD6F6P7c2f4ABCDEFG810 b d +
        quarticCoreD6F6P8c2f4ABCDEFG810 b d +
        quarticCoreD6F6P9c2f4ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c2f4ABCDEFG810, quarticCoreD6F6P2c2f4ABCDEFG810, quarticCoreD6F6P3c2f4ABCDEFG810, quarticCoreD6F6P4c2f4ABCDEFG810, quarticCoreD6F6P5c2f4ABCDEFG810, quarticCoreD6F6P6c2f4ABCDEFG810, quarticCoreD6F6P7c2f4ABCDEFG810, quarticCoreD6F6P8c2f4ABCDEFG810, quarticCoreD6F6P9c2f4ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c2f5
    (b d : k) :
    quarticCoreD6F6P1c2f5ABCDEFG810 b d +
        quarticCoreD6F6P2c2f5ABCDEFG810 b d +
        quarticCoreD6F6P3c2f5ABCDEFG810 b d +
        quarticCoreD6F6P4c2f5ABCDEFG810 b d +
        quarticCoreD6F6P5c2f5ABCDEFG810 b d +
        quarticCoreD6F6P6c2f5ABCDEFG810 b d +
        quarticCoreD6F6P7c2f5ABCDEFG810 b d +
        quarticCoreD6F6P8c2f5ABCDEFG810 b d +
        quarticCoreD6F6P9c2f5ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c2f5ABCDEFG810, quarticCoreD6F6P2c2f5ABCDEFG810, quarticCoreD6F6P3c2f5ABCDEFG810, quarticCoreD6F6P4c2f5ABCDEFG810, quarticCoreD6F6P5c2f5ABCDEFG810, quarticCoreD6F6P6c2f5ABCDEFG810, quarticCoreD6F6P7c2f5ABCDEFG810, quarticCoreD6F6P8c2f5ABCDEFG810, quarticCoreD6F6P9c2f5ABCDEFG810]
  try ring

end QuarticFullConeABCDEFG810D6F6
end Max11DegreeRoutes
end
