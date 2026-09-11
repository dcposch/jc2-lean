import Grok810ScaleZeroQuarticFullConeD6F6Part29Scratch
import Grok810ScaleZeroQuarticFullConeD6F6Part59Scratch
import Grok810ScaleZeroQuarticFullConeD6F6Part60Scratch

/-! Part 61 of 61 of `Grok810ScaleZeroQuarticFullConeD6F6Scratch`, split so that no single module elaborates them all
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
theorem quarticCoreD6F6_combine_c6f2
    (b d : k) :
    quarticCoreD6F6P1c6f2ABCDEFG810 b d +
        quarticCoreD6F6P2c6f2ABCDEFG810 b d +
        quarticCoreD6F6P3c6f2ABCDEFG810 b d +
        quarticCoreD6F6P4c6f2ABCDEFG810 b d +
        quarticCoreD6F6P5c6f2ABCDEFG810 b d +
        quarticCoreD6F6P6c6f2ABCDEFG810 b d +
        quarticCoreD6F6P7c6f2ABCDEFG810 b d +
        quarticCoreD6F6P8c6f2ABCDEFG810 b d +
        quarticCoreD6F6P9c6f2ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c6f2ABCDEFG810, quarticCoreD6F6P2c6f2ABCDEFG810, quarticCoreD6F6P3c6f2ABCDEFG810, quarticCoreD6F6P4c6f2ABCDEFG810, quarticCoreD6F6P5c6f2ABCDEFG810, quarticCoreD6F6P6c6f2ABCDEFG810, quarticCoreD6F6P7c6f2ABCDEFG810, quarticCoreD6F6P8c6f2ABCDEFG810, quarticCoreD6F6P9c6f2ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c6f3
    (b d : k) :
    quarticCoreD6F6P1c6f3ABCDEFG810 b d +
        quarticCoreD6F6P2c6f3ABCDEFG810 b d +
        quarticCoreD6F6P3c6f3ABCDEFG810 b d +
        quarticCoreD6F6P4c6f3ABCDEFG810 b d +
        quarticCoreD6F6P5c6f3ABCDEFG810 b d +
        quarticCoreD6F6P6c6f3ABCDEFG810 b d +
        quarticCoreD6F6P7c6f3ABCDEFG810 b d +
        quarticCoreD6F6P8c6f3ABCDEFG810 b d +
        quarticCoreD6F6P9c6f3ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c6f3ABCDEFG810, quarticCoreD6F6P2c6f3ABCDEFG810, quarticCoreD6F6P3c6f3ABCDEFG810, quarticCoreD6F6P4c6f3ABCDEFG810, quarticCoreD6F6P5c6f3ABCDEFG810, quarticCoreD6F6P6c6f3ABCDEFG810, quarticCoreD6F6P7c6f3ABCDEFG810, quarticCoreD6F6P8c6f3ABCDEFG810, quarticCoreD6F6P9c6f3ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c6f4
    (b d : k) :
    quarticCoreD6F6P1c6f4ABCDEFG810 b d +
        quarticCoreD6F6P2c6f4ABCDEFG810 b d +
        quarticCoreD6F6P3c6f4ABCDEFG810 b d +
        quarticCoreD6F6P4c6f4ABCDEFG810 b d +
        quarticCoreD6F6P5c6f4ABCDEFG810 b d +
        quarticCoreD6F6P6c6f4ABCDEFG810 b d +
        quarticCoreD6F6P7c6f4ABCDEFG810 b d +
        quarticCoreD6F6P8c6f4ABCDEFG810 b d +
        quarticCoreD6F6P9c6f4ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c6f4ABCDEFG810, quarticCoreD6F6P2c6f4ABCDEFG810, quarticCoreD6F6P3c6f4ABCDEFG810, quarticCoreD6F6P4c6f4ABCDEFG810, quarticCoreD6F6P5c6f4ABCDEFG810, quarticCoreD6F6P6c6f4ABCDEFG810, quarticCoreD6F6P7c6f4ABCDEFG810, quarticCoreD6F6P8c6f4ABCDEFG810, quarticCoreD6F6P9c6f4ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c7f0
    (b d : k) :
    quarticCoreD6F6P1c7f0ABCDEFG810 b d +
        quarticCoreD6F6P2c7f0ABCDEFG810 b d +
        quarticCoreD6F6P3c7f0ABCDEFG810 b d +
        quarticCoreD6F6P4c7f0ABCDEFG810 b d +
        quarticCoreD6F6P5c7f0ABCDEFG810 b d +
        quarticCoreD6F6P6c7f0ABCDEFG810 b d +
        quarticCoreD6F6P7c7f0ABCDEFG810 b d +
        quarticCoreD6F6P8c7f0ABCDEFG810 b d +
        quarticCoreD6F6P9c7f0ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c7f0ABCDEFG810, quarticCoreD6F6P2c7f0ABCDEFG810, quarticCoreD6F6P3c7f0ABCDEFG810, quarticCoreD6F6P4c7f0ABCDEFG810, quarticCoreD6F6P5c7f0ABCDEFG810, quarticCoreD6F6P6c7f0ABCDEFG810, quarticCoreD6F6P7c7f0ABCDEFG810, quarticCoreD6F6P8c7f0ABCDEFG810, quarticCoreD6F6P9c7f0ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c7f1
    (b d : k) :
    quarticCoreD6F6P1c7f1ABCDEFG810 b d +
        quarticCoreD6F6P2c7f1ABCDEFG810 b d +
        quarticCoreD6F6P3c7f1ABCDEFG810 b d +
        quarticCoreD6F6P4c7f1ABCDEFG810 b d +
        quarticCoreD6F6P5c7f1ABCDEFG810 b d +
        quarticCoreD6F6P6c7f1ABCDEFG810 b d +
        quarticCoreD6F6P7c7f1ABCDEFG810 b d +
        quarticCoreD6F6P8c7f1ABCDEFG810 b d +
        quarticCoreD6F6P9c7f1ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c7f1ABCDEFG810, quarticCoreD6F6P2c7f1ABCDEFG810, quarticCoreD6F6P3c7f1ABCDEFG810, quarticCoreD6F6P4c7f1ABCDEFG810, quarticCoreD6F6P5c7f1ABCDEFG810, quarticCoreD6F6P6c7f1ABCDEFG810, quarticCoreD6F6P7c7f1ABCDEFG810, quarticCoreD6F6P8c7f1ABCDEFG810, quarticCoreD6F6P9c7f1ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c7f2
    (b d : k) :
    quarticCoreD6F6P1c7f2ABCDEFG810 b d +
        quarticCoreD6F6P2c7f2ABCDEFG810 b d +
        quarticCoreD6F6P3c7f2ABCDEFG810 b d +
        quarticCoreD6F6P4c7f2ABCDEFG810 b d +
        quarticCoreD6F6P5c7f2ABCDEFG810 b d +
        quarticCoreD6F6P6c7f2ABCDEFG810 b d +
        quarticCoreD6F6P7c7f2ABCDEFG810 b d +
        quarticCoreD6F6P8c7f2ABCDEFG810 b d +
        quarticCoreD6F6P9c7f2ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c7f2ABCDEFG810, quarticCoreD6F6P2c7f2ABCDEFG810, quarticCoreD6F6P3c7f2ABCDEFG810, quarticCoreD6F6P4c7f2ABCDEFG810, quarticCoreD6F6P5c7f2ABCDEFG810, quarticCoreD6F6P6c7f2ABCDEFG810, quarticCoreD6F6P7c7f2ABCDEFG810, quarticCoreD6F6P8c7f2ABCDEFG810, quarticCoreD6F6P9c7f2ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c7f3
    (b d : k) :
    quarticCoreD6F6P1c7f3ABCDEFG810 b d +
        quarticCoreD6F6P2c7f3ABCDEFG810 b d +
        quarticCoreD6F6P3c7f3ABCDEFG810 b d +
        quarticCoreD6F6P4c7f3ABCDEFG810 b d +
        quarticCoreD6F6P5c7f3ABCDEFG810 b d +
        quarticCoreD6F6P6c7f3ABCDEFG810 b d +
        quarticCoreD6F6P7c7f3ABCDEFG810 b d +
        quarticCoreD6F6P8c7f3ABCDEFG810 b d +
        quarticCoreD6F6P9c7f3ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c7f3ABCDEFG810, quarticCoreD6F6P2c7f3ABCDEFG810, quarticCoreD6F6P3c7f3ABCDEFG810, quarticCoreD6F6P4c7f3ABCDEFG810, quarticCoreD6F6P5c7f3ABCDEFG810, quarticCoreD6F6P6c7f3ABCDEFG810, quarticCoreD6F6P7c7f3ABCDEFG810, quarticCoreD6F6P8c7f3ABCDEFG810, quarticCoreD6F6P9c7f3ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c8f0
    (b d : k) :
    quarticCoreD6F6P1c8f0ABCDEFG810 b d +
        quarticCoreD6F6P2c8f0ABCDEFG810 b d +
        quarticCoreD6F6P3c8f0ABCDEFG810 b d +
        quarticCoreD6F6P4c8f0ABCDEFG810 b d +
        quarticCoreD6F6P5c8f0ABCDEFG810 b d +
        quarticCoreD6F6P6c8f0ABCDEFG810 b d +
        quarticCoreD6F6P7c8f0ABCDEFG810 b d +
        quarticCoreD6F6P8c8f0ABCDEFG810 b d +
        quarticCoreD6F6P9c8f0ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c8f0ABCDEFG810, quarticCoreD6F6P2c8f0ABCDEFG810, quarticCoreD6F6P3c8f0ABCDEFG810, quarticCoreD6F6P4c8f0ABCDEFG810, quarticCoreD6F6P5c8f0ABCDEFG810, quarticCoreD6F6P6c8f0ABCDEFG810, quarticCoreD6F6P7c8f0ABCDEFG810, quarticCoreD6F6P8c8f0ABCDEFG810, quarticCoreD6F6P9c8f0ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c8f1
    (b d : k) :
    quarticCoreD6F6P1c8f1ABCDEFG810 b d +
        quarticCoreD6F6P2c8f1ABCDEFG810 b d +
        quarticCoreD6F6P3c8f1ABCDEFG810 b d +
        quarticCoreD6F6P4c8f1ABCDEFG810 b d +
        quarticCoreD6F6P5c8f1ABCDEFG810 b d +
        quarticCoreD6F6P6c8f1ABCDEFG810 b d +
        quarticCoreD6F6P7c8f1ABCDEFG810 b d +
        quarticCoreD6F6P8c8f1ABCDEFG810 b d +
        quarticCoreD6F6P9c8f1ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c8f1ABCDEFG810, quarticCoreD6F6P2c8f1ABCDEFG810, quarticCoreD6F6P3c8f1ABCDEFG810, quarticCoreD6F6P4c8f1ABCDEFG810, quarticCoreD6F6P5c8f1ABCDEFG810, quarticCoreD6F6P6c8f1ABCDEFG810, quarticCoreD6F6P7c8f1ABCDEFG810, quarticCoreD6F6P8c8f1ABCDEFG810, quarticCoreD6F6P9c8f1ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c8f2
    (b d : k) :
    quarticCoreD6F6P1c8f2ABCDEFG810 b d +
        quarticCoreD6F6P2c8f2ABCDEFG810 b d +
        quarticCoreD6F6P3c8f2ABCDEFG810 b d +
        quarticCoreD6F6P4c8f2ABCDEFG810 b d +
        quarticCoreD6F6P5c8f2ABCDEFG810 b d +
        quarticCoreD6F6P6c8f2ABCDEFG810 b d +
        quarticCoreD6F6P7c8f2ABCDEFG810 b d +
        quarticCoreD6F6P8c8f2ABCDEFG810 b d +
        quarticCoreD6F6P9c8f2ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c8f2ABCDEFG810, quarticCoreD6F6P2c8f2ABCDEFG810, quarticCoreD6F6P3c8f2ABCDEFG810, quarticCoreD6F6P4c8f2ABCDEFG810, quarticCoreD6F6P5c8f2ABCDEFG810, quarticCoreD6F6P6c8f2ABCDEFG810, quarticCoreD6F6P7c8f2ABCDEFG810, quarticCoreD6F6P8c8f2ABCDEFG810, quarticCoreD6F6P9c8f2ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c9f0
    (b d : k) :
    quarticCoreD6F6P1c9f0ABCDEFG810 b d +
        quarticCoreD6F6P2c9f0ABCDEFG810 b d +
        quarticCoreD6F6P3c9f0ABCDEFG810 b d +
        quarticCoreD6F6P4c9f0ABCDEFG810 b d +
        quarticCoreD6F6P5c9f0ABCDEFG810 b d +
        quarticCoreD6F6P6c9f0ABCDEFG810 b d +
        quarticCoreD6F6P7c9f0ABCDEFG810 b d +
        quarticCoreD6F6P8c9f0ABCDEFG810 b d +
        quarticCoreD6F6P9c9f0ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c9f0ABCDEFG810, quarticCoreD6F6P2c9f0ABCDEFG810, quarticCoreD6F6P3c9f0ABCDEFG810, quarticCoreD6F6P4c9f0ABCDEFG810, quarticCoreD6F6P5c9f0ABCDEFG810, quarticCoreD6F6P6c9f0ABCDEFG810, quarticCoreD6F6P7c9f0ABCDEFG810, quarticCoreD6F6P8c9f0ABCDEFG810, quarticCoreD6F6P9c9f0ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c9f1
    (b d : k) :
    quarticCoreD6F6P1c9f1ABCDEFG810 b d +
        quarticCoreD6F6P2c9f1ABCDEFG810 b d +
        quarticCoreD6F6P3c9f1ABCDEFG810 b d +
        quarticCoreD6F6P4c9f1ABCDEFG810 b d +
        quarticCoreD6F6P5c9f1ABCDEFG810 b d +
        quarticCoreD6F6P6c9f1ABCDEFG810 b d +
        quarticCoreD6F6P7c9f1ABCDEFG810 b d +
        quarticCoreD6F6P8c9f1ABCDEFG810 b d +
        quarticCoreD6F6P9c9f1ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c9f1ABCDEFG810, quarticCoreD6F6P2c9f1ABCDEFG810, quarticCoreD6F6P3c9f1ABCDEFG810, quarticCoreD6F6P4c9f1ABCDEFG810, quarticCoreD6F6P5c9f1ABCDEFG810, quarticCoreD6F6P6c9f1ABCDEFG810, quarticCoreD6F6P7c9f1ABCDEFG810, quarticCoreD6F6P8c9f1ABCDEFG810, quarticCoreD6F6P9c9f1ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c10f0
    (b d : k) :
    quarticCoreD6F6P1c10f0ABCDEFG810 b d +
        quarticCoreD6F6P2c10f0ABCDEFG810 b d +
        quarticCoreD6F6P3c10f0ABCDEFG810 b d +
        quarticCoreD6F6P4c10f0ABCDEFG810 b d +
        quarticCoreD6F6P5c10f0ABCDEFG810 b d +
        quarticCoreD6F6P6c10f0ABCDEFG810 b d +
        quarticCoreD6F6P7c10f0ABCDEFG810 b d +
        quarticCoreD6F6P8c10f0ABCDEFG810 b d +
        quarticCoreD6F6P9c10f0ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c10f0ABCDEFG810, quarticCoreD6F6P2c10f0ABCDEFG810, quarticCoreD6F6P3c10f0ABCDEFG810, quarticCoreD6F6P4c10f0ABCDEFG810, quarticCoreD6F6P5c10f0ABCDEFG810, quarticCoreD6F6P6c10f0ABCDEFG810, quarticCoreD6F6P7c10f0ABCDEFG810, quarticCoreD6F6P8c10f0ABCDEFG810, quarticCoreD6F6P9c10f0ABCDEFG810]
  try ring

/-! ## The nine-product identity -/
set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_identity
    (b c d f : k) :
    quarticCoreD6F6A1ABCDEFG810 b c d f * quarticCoreD1ABCDEFG810 b c d f +
        quarticCoreD6F6A2ABCDEFG810 b c d f * quarticCoreResE_U22_TABCDEFG810 b c d f +
        quarticCoreD6F6A3ABCDEFG810 b c d f * quarticCoreResE_T_U25aABCDEFG810 b c d f +
        quarticCoreD6F6A4ABCDEFG810 b c d f * quarticCoreResE_U22_VABCDEFG810 b c d f +
        quarticCoreD6F6A5ABCDEFG810 b c d f * quarticCoreResE_U25a_VABCDEFG810 b c d f +
        quarticCoreD6F6A6ABCDEFG810 b c d f * quarticCoreResE_U22_U24ABCDEFG810 b c d f +
        quarticCoreD6F6A7ABCDEFG810 b c d f * quarticCoreResE_T_VABCDEFG810 b c d f +
        quarticCoreD6F6A8ABCDEFG810 b c d f * quarticCoreResE_U25a_U24ABCDEFG810 b c d f +
        quarticCoreD6F6A9ABCDEFG810 b c d f * quarticCoreResE_U22_U25bABCDEFG810 b c d f =
      (quarticCoreD6F6NABCDEFG810 : k) * d ^ 6 * f ^ 6 := by
  rw [quarticCoreD6F6P1_eq_viaf, quarticCoreD6F6P2_eq_viaf, quarticCoreD6F6P3_eq_viaf, quarticCoreD6F6P4_eq_viaf, quarticCoreD6F6P5_eq_viaf, quarticCoreD6F6P6_eq_viaf, quarticCoreD6F6P7_eq_viaf, quarticCoreD6F6P8_eq_viaf, quarticCoreD6F6P9_eq_viaf]
  rw [quarticCoreD6F6P1viaABCDEFG810, quarticCoreD6F6P2viaABCDEFG810, quarticCoreD6F6P3viaABCDEFG810, quarticCoreD6F6P4viaABCDEFG810, quarticCoreD6F6P5viaABCDEFG810, quarticCoreD6F6P6viaABCDEFG810, quarticCoreD6F6P7viaABCDEFG810, quarticCoreD6F6P8viaABCDEFG810, quarticCoreD6F6P9viaABCDEFG810]
  have h0t0 := quarticCoreD6F6_combine_c0f0 b d
  have h0t1 := quarticCoreD6F6_combine_c0f1 b d
  have h0t2 := quarticCoreD6F6_combine_c0f2 b d
  have h0t3 := quarticCoreD6F6_combine_c0f3 b d
  have h0t4 := quarticCoreD6F6_combine_c0f4 b d
  have h0t5 := quarticCoreD6F6_combine_c0f5 b d
  have h0t6 := quarticCoreD6F6_combine_c0f6 b d
  have h0t7 := quarticCoreD6F6_combine_c0f7 b d
  have h0t8 := quarticCoreD6F6_combine_c0f8 b d
  have h1t0 := quarticCoreD6F6_combine_c1f0 b d
  have h1t1 := quarticCoreD6F6_combine_c1f1 b d
  have h1t2 := quarticCoreD6F6_combine_c1f2 b d
  have h1t3 := quarticCoreD6F6_combine_c1f3 b d
  have h1t4 := quarticCoreD6F6_combine_c1f4 b d
  have h1t5 := quarticCoreD6F6_combine_c1f5 b d
  have h1t6 := quarticCoreD6F6_combine_c1f6 b d
  have h1t7 := quarticCoreD6F6_combine_c1f7 b d
  have h1t8 := quarticCoreD6F6_combine_c1f8 b d
  have h2t0 := quarticCoreD6F6_combine_c2f0 b d
  have h2t1 := quarticCoreD6F6_combine_c2f1 b d
  have h2t2 := quarticCoreD6F6_combine_c2f2 b d
  have h2t3 := quarticCoreD6F6_combine_c2f3 b d
  have h2t4 := quarticCoreD6F6_combine_c2f4 b d
  have h2t5 := quarticCoreD6F6_combine_c2f5 b d
  have h2t6 := quarticCoreD6F6_combine_c2f6 b d
  have h2t7 := quarticCoreD6F6_combine_c2f7 b d
  have h3t0 := quarticCoreD6F6_combine_c3f0 b d
  have h3t1 := quarticCoreD6F6_combine_c3f1 b d
  have h3t2 := quarticCoreD6F6_combine_c3f2 b d
  have h3t3 := quarticCoreD6F6_combine_c3f3 b d
  have h3t4 := quarticCoreD6F6_combine_c3f4 b d
  have h3t5 := quarticCoreD6F6_combine_c3f5 b d
  have h3t6 := quarticCoreD6F6_combine_c3f6 b d
  have h3t7 := quarticCoreD6F6_combine_c3f7 b d
  have h4t0 := quarticCoreD6F6_combine_c4f0 b d
  have h4t1 := quarticCoreD6F6_combine_c4f1 b d
  have h4t2 := quarticCoreD6F6_combine_c4f2 b d
  have h4t3 := quarticCoreD6F6_combine_c4f3 b d
  have h4t4 := quarticCoreD6F6_combine_c4f4 b d
  have h4t5 := quarticCoreD6F6_combine_c4f5 b d
  have h4t6 := quarticCoreD6F6_combine_c4f6 b d
  have h5t0 := quarticCoreD6F6_combine_c5f0 b d
  have h5t1 := quarticCoreD6F6_combine_c5f1 b d
  have h5t2 := quarticCoreD6F6_combine_c5f2 b d
  have h5t3 := quarticCoreD6F6_combine_c5f3 b d
  have h5t4 := quarticCoreD6F6_combine_c5f4 b d
  have h5t5 := quarticCoreD6F6_combine_c5f5 b d
  have h6t0 := quarticCoreD6F6_combine_c6f0 b d
  have h6t1 := quarticCoreD6F6_combine_c6f1 b d
  have h6t2 := quarticCoreD6F6_combine_c6f2 b d
  have h6t3 := quarticCoreD6F6_combine_c6f3 b d
  have h6t4 := quarticCoreD6F6_combine_c6f4 b d
  have h7t0 := quarticCoreD6F6_combine_c7f0 b d
  have h7t1 := quarticCoreD6F6_combine_c7f1 b d
  have h7t2 := quarticCoreD6F6_combine_c7f2 b d
  have h7t3 := quarticCoreD6F6_combine_c7f3 b d
  have h8t0 := quarticCoreD6F6_combine_c8f0 b d
  have h8t1 := quarticCoreD6F6_combine_c8f1 b d
  have h8t2 := quarticCoreD6F6_combine_c8f2 b d
  have h9t0 := quarticCoreD6F6_combine_c9f0 b d
  have h9t1 := quarticCoreD6F6_combine_c9f1 b d
  have h10t0 := quarticCoreD6F6_combine_c10f0 b d
  linear_combination (norm := skip)
      h0t0 +
      h0t1 * f +
      h0t2 * f ^ 2 +
      h0t3 * f ^ 3 +
      h0t4 * f ^ 4 +
      h0t5 * f ^ 5 +
      h0t6 * f ^ 6 +
      h0t7 * f ^ 7 +
      h0t8 * f ^ 8 +
      h1t0 * c +
      h1t1 * c * f +
      h1t2 * c * f ^ 2 +
      h1t3 * c * f ^ 3 +
      h1t4 * c * f ^ 4 +
      h1t5 * c * f ^ 5 +
      h1t6 * c * f ^ 6 +
      h1t7 * c * f ^ 7 +
      h1t8 * c * f ^ 8 +
      h2t0 * c ^ 2 +
      h2t1 * c ^ 2 * f +
      h2t2 * c ^ 2 * f ^ 2 +
      h2t3 * c ^ 2 * f ^ 3 +
      h2t4 * c ^ 2 * f ^ 4 +
      h2t5 * c ^ 2 * f ^ 5 +
      h2t6 * c ^ 2 * f ^ 6 +
      h2t7 * c ^ 2 * f ^ 7 +
      h3t0 * c ^ 3 +
      h3t1 * c ^ 3 * f +
      h3t2 * c ^ 3 * f ^ 2 +
      h3t3 * c ^ 3 * f ^ 3 +
      h3t4 * c ^ 3 * f ^ 4 +
      h3t5 * c ^ 3 * f ^ 5 +
      h3t6 * c ^ 3 * f ^ 6 +
      h3t7 * c ^ 3 * f ^ 7 +
      h4t0 * c ^ 4 +
      h4t1 * c ^ 4 * f +
      h4t2 * c ^ 4 * f ^ 2 +
      h4t3 * c ^ 4 * f ^ 3 +
      h4t4 * c ^ 4 * f ^ 4 +
      h4t5 * c ^ 4 * f ^ 5 +
      h4t6 * c ^ 4 * f ^ 6 +
      h5t0 * c ^ 5 +
      h5t1 * c ^ 5 * f +
      h5t2 * c ^ 5 * f ^ 2 +
      h5t3 * c ^ 5 * f ^ 3 +
      h5t4 * c ^ 5 * f ^ 4 +
      h5t5 * c ^ 5 * f ^ 5 +
      h6t0 * c ^ 6 +
      h6t1 * c ^ 6 * f +
      h6t2 * c ^ 6 * f ^ 2 +
      h6t3 * c ^ 6 * f ^ 3 +
      h6t4 * c ^ 6 * f ^ 4 +
      h7t0 * c ^ 7 +
      h7t1 * c ^ 7 * f +
      h7t2 * c ^ 7 * f ^ 2 +
      h7t3 * c ^ 7 * f ^ 3 +
      h8t0 * c ^ 8 +
      h8t1 * c ^ 8 * f +
      h8t2 * c ^ 8 * f ^ 2 +
      h9t0 * c ^ 9 +
      h9t1 * c ^ 9 * f +
      h10t0 * c ^ 10
  ring

/-! ## The cone is empty -/

set_option maxHeartbeats 64000000 in
theorem quarticConeABCDEFG810_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEFG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  obtain ⟨_, _, _, _, _, _, _, _, hE1, hE2, hE3, hE4, hE5, hE6, hE7, hE8, hE9, _, _, _⟩ :=
    quarticConeABCDEFG810_residual3 (j := j) (t := t) l beta gamma delta epsilon zeta eta theta
      A B C D E F G hcone hxi hmu homi hkap hnu hpi hjdiv hder
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, _⟩
    omega
  have hDlc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hFpos, hGpos, _⟩
    omega
  have hFlc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hid := quarticCoreD6F6_identity B.leadingCoeff C.leadingCoeff D.leadingCoeff
      F.leadingCoeff
  have key : (quarticCoreD6F6NABCDEFG810 : k) * D.leadingCoeff ^ 6 * F.leadingCoeff ^ 6 = 0 := by
    rw [← hid]
    linear_combination
        (quarticCoreD6F6A1ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff
            F.leadingCoeff) * hE1 +
        (quarticCoreD6F6A2ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff
            F.leadingCoeff) * hE2 +
        (quarticCoreD6F6A3ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff
            F.leadingCoeff) * hE3 +
        (quarticCoreD6F6A4ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff
            F.leadingCoeff) * hE4 +
        (quarticCoreD6F6A5ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff
            F.leadingCoeff) * hE5 +
        (quarticCoreD6F6A6ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff
            F.leadingCoeff) * hE6 +
        (quarticCoreD6F6A7ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff
            F.leadingCoeff) * hE7 +
        (quarticCoreD6F6A8ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff
            F.leadingCoeff) * hE8 +
        (quarticCoreD6F6A9ABCDEFG810 B.leadingCoeff C.leadingCoeff D.leadingCoeff
            F.leadingCoeff) * hE9
  have hN : (quarticCoreD6F6NABCDEFG810 : k) ≠ 0 := by
    refine Nat.cast_ne_zero.mpr ?_
    unfold quarticCoreD6F6NABCDEFG810
    norm_num
  have hne : (quarticCoreD6F6NABCDEFG810 : k) * D.leadingCoeff ^ 6 * F.leadingCoeff ^ 6 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hN (pow_ne_zero 6 hDlc)) (pow_ne_zero 6 hFlc)
  exact hne key


end QuarticFullConeABCDEFG810D6F6
end Max11DegreeRoutes
end
