import Grok810ScaleZeroQuarticFullConeD6F6Part59Scratch

/-! Part 60 of 61 of `Grok810ScaleZeroQuarticFullConeD6F6Scratch`, split so that no single module elaborates them all
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
theorem quarticCoreD6F6_combine_c2f6
    (b d : k) :
    quarticCoreD6F6P1c2f6ABCDEFG810 b d +
        quarticCoreD6F6P2c2f6ABCDEFG810 b d +
        quarticCoreD6F6P3c2f6ABCDEFG810 b d +
        quarticCoreD6F6P4c2f6ABCDEFG810 b d +
        quarticCoreD6F6P5c2f6ABCDEFG810 b d +
        quarticCoreD6F6P6c2f6ABCDEFG810 b d +
        quarticCoreD6F6P7c2f6ABCDEFG810 b d +
        quarticCoreD6F6P8c2f6ABCDEFG810 b d +
        quarticCoreD6F6P9c2f6ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c2f6ABCDEFG810, quarticCoreD6F6P2c2f6ABCDEFG810, quarticCoreD6F6P3c2f6ABCDEFG810, quarticCoreD6F6P4c2f6ABCDEFG810, quarticCoreD6F6P5c2f6ABCDEFG810, quarticCoreD6F6P6c2f6ABCDEFG810, quarticCoreD6F6P7c2f6ABCDEFG810, quarticCoreD6F6P8c2f6ABCDEFG810, quarticCoreD6F6P9c2f6ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c2f7
    (b d : k) :
    quarticCoreD6F6P4c2f7ABCDEFG810 b d +
        quarticCoreD6F6P5c2f7ABCDEFG810 b d +
        quarticCoreD6F6P6c2f7ABCDEFG810 b d +
        quarticCoreD6F6P7c2f7ABCDEFG810 b d +
        quarticCoreD6F6P8c2f7ABCDEFG810 b d +
        quarticCoreD6F6P9c2f7ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P4c2f7ABCDEFG810, quarticCoreD6F6P5c2f7ABCDEFG810, quarticCoreD6F6P6c2f7ABCDEFG810, quarticCoreD6F6P7c2f7ABCDEFG810, quarticCoreD6F6P8c2f7ABCDEFG810, quarticCoreD6F6P9c2f7ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c3f0
    (b d : k) :
    quarticCoreD6F6P1c3f0ABCDEFG810 b d +
        quarticCoreD6F6P2c3f0ABCDEFG810 b d +
        quarticCoreD6F6P3c3f0ABCDEFG810 b d +
        quarticCoreD6F6P4c3f0ABCDEFG810 b d +
        quarticCoreD6F6P5c3f0ABCDEFG810 b d +
        quarticCoreD6F6P6c3f0ABCDEFG810 b d +
        quarticCoreD6F6P7c3f0ABCDEFG810 b d +
        quarticCoreD6F6P8c3f0ABCDEFG810 b d +
        quarticCoreD6F6P9c3f0ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c3f0ABCDEFG810, quarticCoreD6F6P2c3f0ABCDEFG810, quarticCoreD6F6P3c3f0ABCDEFG810, quarticCoreD6F6P4c3f0ABCDEFG810, quarticCoreD6F6P5c3f0ABCDEFG810, quarticCoreD6F6P6c3f0ABCDEFG810, quarticCoreD6F6P7c3f0ABCDEFG810, quarticCoreD6F6P8c3f0ABCDEFG810, quarticCoreD6F6P9c3f0ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c3f1
    (b d : k) :
    quarticCoreD6F6P1c3f1ABCDEFG810 b d +
        quarticCoreD6F6P2c3f1ABCDEFG810 b d +
        quarticCoreD6F6P3c3f1ABCDEFG810 b d +
        quarticCoreD6F6P4c3f1ABCDEFG810 b d +
        quarticCoreD6F6P5c3f1ABCDEFG810 b d +
        quarticCoreD6F6P6c3f1ABCDEFG810 b d +
        quarticCoreD6F6P7c3f1ABCDEFG810 b d +
        quarticCoreD6F6P8c3f1ABCDEFG810 b d +
        quarticCoreD6F6P9c3f1ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c3f1ABCDEFG810, quarticCoreD6F6P2c3f1ABCDEFG810, quarticCoreD6F6P3c3f1ABCDEFG810, quarticCoreD6F6P4c3f1ABCDEFG810, quarticCoreD6F6P5c3f1ABCDEFG810, quarticCoreD6F6P6c3f1ABCDEFG810, quarticCoreD6F6P7c3f1ABCDEFG810, quarticCoreD6F6P8c3f1ABCDEFG810, quarticCoreD6F6P9c3f1ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c3f2
    (b d : k) :
    quarticCoreD6F6P1c3f2ABCDEFG810 b d +
        quarticCoreD6F6P2c3f2ABCDEFG810 b d +
        quarticCoreD6F6P3c3f2ABCDEFG810 b d +
        quarticCoreD6F6P4c3f2ABCDEFG810 b d +
        quarticCoreD6F6P5c3f2ABCDEFG810 b d +
        quarticCoreD6F6P6c3f2ABCDEFG810 b d +
        quarticCoreD6F6P7c3f2ABCDEFG810 b d +
        quarticCoreD6F6P8c3f2ABCDEFG810 b d +
        quarticCoreD6F6P9c3f2ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c3f2ABCDEFG810, quarticCoreD6F6P2c3f2ABCDEFG810, quarticCoreD6F6P3c3f2ABCDEFG810, quarticCoreD6F6P4c3f2ABCDEFG810, quarticCoreD6F6P5c3f2ABCDEFG810, quarticCoreD6F6P6c3f2ABCDEFG810, quarticCoreD6F6P7c3f2ABCDEFG810, quarticCoreD6F6P8c3f2ABCDEFG810, quarticCoreD6F6P9c3f2ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c3f3
    (b d : k) :
    quarticCoreD6F6P1c3f3ABCDEFG810 b d +
        quarticCoreD6F6P2c3f3ABCDEFG810 b d +
        quarticCoreD6F6P3c3f3ABCDEFG810 b d +
        quarticCoreD6F6P4c3f3ABCDEFG810 b d +
        quarticCoreD6F6P5c3f3ABCDEFG810 b d +
        quarticCoreD6F6P6c3f3ABCDEFG810 b d +
        quarticCoreD6F6P7c3f3ABCDEFG810 b d +
        quarticCoreD6F6P8c3f3ABCDEFG810 b d +
        quarticCoreD6F6P9c3f3ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c3f3ABCDEFG810, quarticCoreD6F6P2c3f3ABCDEFG810, quarticCoreD6F6P3c3f3ABCDEFG810, quarticCoreD6F6P4c3f3ABCDEFG810, quarticCoreD6F6P5c3f3ABCDEFG810, quarticCoreD6F6P6c3f3ABCDEFG810, quarticCoreD6F6P7c3f3ABCDEFG810, quarticCoreD6F6P8c3f3ABCDEFG810, quarticCoreD6F6P9c3f3ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c3f4
    (b d : k) :
    quarticCoreD6F6P1c3f4ABCDEFG810 b d +
        quarticCoreD6F6P2c3f4ABCDEFG810 b d +
        quarticCoreD6F6P3c3f4ABCDEFG810 b d +
        quarticCoreD6F6P4c3f4ABCDEFG810 b d +
        quarticCoreD6F6P5c3f4ABCDEFG810 b d +
        quarticCoreD6F6P6c3f4ABCDEFG810 b d +
        quarticCoreD6F6P7c3f4ABCDEFG810 b d +
        quarticCoreD6F6P8c3f4ABCDEFG810 b d +
        quarticCoreD6F6P9c3f4ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c3f4ABCDEFG810, quarticCoreD6F6P2c3f4ABCDEFG810, quarticCoreD6F6P3c3f4ABCDEFG810, quarticCoreD6F6P4c3f4ABCDEFG810, quarticCoreD6F6P5c3f4ABCDEFG810, quarticCoreD6F6P6c3f4ABCDEFG810, quarticCoreD6F6P7c3f4ABCDEFG810, quarticCoreD6F6P8c3f4ABCDEFG810, quarticCoreD6F6P9c3f4ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c3f5
    (b d : k) :
    quarticCoreD6F6P1c3f5ABCDEFG810 b d +
        quarticCoreD6F6P2c3f5ABCDEFG810 b d +
        quarticCoreD6F6P3c3f5ABCDEFG810 b d +
        quarticCoreD6F6P4c3f5ABCDEFG810 b d +
        quarticCoreD6F6P5c3f5ABCDEFG810 b d +
        quarticCoreD6F6P6c3f5ABCDEFG810 b d +
        quarticCoreD6F6P7c3f5ABCDEFG810 b d +
        quarticCoreD6F6P8c3f5ABCDEFG810 b d +
        quarticCoreD6F6P9c3f5ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c3f5ABCDEFG810, quarticCoreD6F6P2c3f5ABCDEFG810, quarticCoreD6F6P3c3f5ABCDEFG810, quarticCoreD6F6P4c3f5ABCDEFG810, quarticCoreD6F6P5c3f5ABCDEFG810, quarticCoreD6F6P6c3f5ABCDEFG810, quarticCoreD6F6P7c3f5ABCDEFG810, quarticCoreD6F6P8c3f5ABCDEFG810, quarticCoreD6F6P9c3f5ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c3f6
    (b d : k) :
    quarticCoreD6F6P1c3f6ABCDEFG810 b d +
        quarticCoreD6F6P2c3f6ABCDEFG810 b d +
        quarticCoreD6F6P3c3f6ABCDEFG810 b d +
        quarticCoreD6F6P4c3f6ABCDEFG810 b d +
        quarticCoreD6F6P5c3f6ABCDEFG810 b d +
        quarticCoreD6F6P6c3f6ABCDEFG810 b d +
        quarticCoreD6F6P7c3f6ABCDEFG810 b d +
        quarticCoreD6F6P8c3f6ABCDEFG810 b d +
        quarticCoreD6F6P9c3f6ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c3f6ABCDEFG810, quarticCoreD6F6P2c3f6ABCDEFG810, quarticCoreD6F6P3c3f6ABCDEFG810, quarticCoreD6F6P4c3f6ABCDEFG810, quarticCoreD6F6P5c3f6ABCDEFG810, quarticCoreD6F6P6c3f6ABCDEFG810, quarticCoreD6F6P7c3f6ABCDEFG810, quarticCoreD6F6P8c3f6ABCDEFG810, quarticCoreD6F6P9c3f6ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c3f7
    (b d : k) :
    quarticCoreD6F6P1c3f7ABCDEFG810 b d +
        quarticCoreD6F6P2c3f7ABCDEFG810 b d +
        quarticCoreD6F6P3c3f7ABCDEFG810 b d +
        quarticCoreD6F6P7c3f7ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c3f7ABCDEFG810, quarticCoreD6F6P2c3f7ABCDEFG810, quarticCoreD6F6P3c3f7ABCDEFG810, quarticCoreD6F6P7c3f7ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c4f0
    (b d : k) :
    quarticCoreD6F6P1c4f0ABCDEFG810 b d +
        quarticCoreD6F6P2c4f0ABCDEFG810 b d +
        quarticCoreD6F6P3c4f0ABCDEFG810 b d +
        quarticCoreD6F6P4c4f0ABCDEFG810 b d +
        quarticCoreD6F6P5c4f0ABCDEFG810 b d +
        quarticCoreD6F6P6c4f0ABCDEFG810 b d +
        quarticCoreD6F6P7c4f0ABCDEFG810 b d +
        quarticCoreD6F6P8c4f0ABCDEFG810 b d +
        quarticCoreD6F6P9c4f0ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c4f0ABCDEFG810, quarticCoreD6F6P2c4f0ABCDEFG810, quarticCoreD6F6P3c4f0ABCDEFG810, quarticCoreD6F6P4c4f0ABCDEFG810, quarticCoreD6F6P5c4f0ABCDEFG810, quarticCoreD6F6P6c4f0ABCDEFG810, quarticCoreD6F6P7c4f0ABCDEFG810, quarticCoreD6F6P8c4f0ABCDEFG810, quarticCoreD6F6P9c4f0ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c4f1
    (b d : k) :
    quarticCoreD6F6P1c4f1ABCDEFG810 b d +
        quarticCoreD6F6P2c4f1ABCDEFG810 b d +
        quarticCoreD6F6P3c4f1ABCDEFG810 b d +
        quarticCoreD6F6P4c4f1ABCDEFG810 b d +
        quarticCoreD6F6P5c4f1ABCDEFG810 b d +
        quarticCoreD6F6P6c4f1ABCDEFG810 b d +
        quarticCoreD6F6P7c4f1ABCDEFG810 b d +
        quarticCoreD6F6P8c4f1ABCDEFG810 b d +
        quarticCoreD6F6P9c4f1ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c4f1ABCDEFG810, quarticCoreD6F6P2c4f1ABCDEFG810, quarticCoreD6F6P3c4f1ABCDEFG810, quarticCoreD6F6P4c4f1ABCDEFG810, quarticCoreD6F6P5c4f1ABCDEFG810, quarticCoreD6F6P6c4f1ABCDEFG810, quarticCoreD6F6P7c4f1ABCDEFG810, quarticCoreD6F6P8c4f1ABCDEFG810, quarticCoreD6F6P9c4f1ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c4f2
    (b d : k) :
    quarticCoreD6F6P1c4f2ABCDEFG810 b d +
        quarticCoreD6F6P2c4f2ABCDEFG810 b d +
        quarticCoreD6F6P3c4f2ABCDEFG810 b d +
        quarticCoreD6F6P4c4f2ABCDEFG810 b d +
        quarticCoreD6F6P5c4f2ABCDEFG810 b d +
        quarticCoreD6F6P6c4f2ABCDEFG810 b d +
        quarticCoreD6F6P7c4f2ABCDEFG810 b d +
        quarticCoreD6F6P8c4f2ABCDEFG810 b d +
        quarticCoreD6F6P9c4f2ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c4f2ABCDEFG810, quarticCoreD6F6P2c4f2ABCDEFG810, quarticCoreD6F6P3c4f2ABCDEFG810, quarticCoreD6F6P4c4f2ABCDEFG810, quarticCoreD6F6P5c4f2ABCDEFG810, quarticCoreD6F6P6c4f2ABCDEFG810, quarticCoreD6F6P7c4f2ABCDEFG810, quarticCoreD6F6P8c4f2ABCDEFG810, quarticCoreD6F6P9c4f2ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c4f3
    (b d : k) :
    quarticCoreD6F6P1c4f3ABCDEFG810 b d +
        quarticCoreD6F6P2c4f3ABCDEFG810 b d +
        quarticCoreD6F6P3c4f3ABCDEFG810 b d +
        quarticCoreD6F6P4c4f3ABCDEFG810 b d +
        quarticCoreD6F6P5c4f3ABCDEFG810 b d +
        quarticCoreD6F6P6c4f3ABCDEFG810 b d +
        quarticCoreD6F6P7c4f3ABCDEFG810 b d +
        quarticCoreD6F6P8c4f3ABCDEFG810 b d +
        quarticCoreD6F6P9c4f3ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c4f3ABCDEFG810, quarticCoreD6F6P2c4f3ABCDEFG810, quarticCoreD6F6P3c4f3ABCDEFG810, quarticCoreD6F6P4c4f3ABCDEFG810, quarticCoreD6F6P5c4f3ABCDEFG810, quarticCoreD6F6P6c4f3ABCDEFG810, quarticCoreD6F6P7c4f3ABCDEFG810, quarticCoreD6F6P8c4f3ABCDEFG810, quarticCoreD6F6P9c4f3ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c4f4
    (b d : k) :
    quarticCoreD6F6P1c4f4ABCDEFG810 b d +
        quarticCoreD6F6P2c4f4ABCDEFG810 b d +
        quarticCoreD6F6P3c4f4ABCDEFG810 b d +
        quarticCoreD6F6P4c4f4ABCDEFG810 b d +
        quarticCoreD6F6P5c4f4ABCDEFG810 b d +
        quarticCoreD6F6P6c4f4ABCDEFG810 b d +
        quarticCoreD6F6P7c4f4ABCDEFG810 b d +
        quarticCoreD6F6P8c4f4ABCDEFG810 b d +
        quarticCoreD6F6P9c4f4ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c4f4ABCDEFG810, quarticCoreD6F6P2c4f4ABCDEFG810, quarticCoreD6F6P3c4f4ABCDEFG810, quarticCoreD6F6P4c4f4ABCDEFG810, quarticCoreD6F6P5c4f4ABCDEFG810, quarticCoreD6F6P6c4f4ABCDEFG810, quarticCoreD6F6P7c4f4ABCDEFG810, quarticCoreD6F6P8c4f4ABCDEFG810, quarticCoreD6F6P9c4f4ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c4f5
    (b d : k) :
    quarticCoreD6F6P1c4f5ABCDEFG810 b d +
        quarticCoreD6F6P2c4f5ABCDEFG810 b d +
        quarticCoreD6F6P3c4f5ABCDEFG810 b d +
        quarticCoreD6F6P4c4f5ABCDEFG810 b d +
        quarticCoreD6F6P5c4f5ABCDEFG810 b d +
        quarticCoreD6F6P6c4f5ABCDEFG810 b d +
        quarticCoreD6F6P7c4f5ABCDEFG810 b d +
        quarticCoreD6F6P8c4f5ABCDEFG810 b d +
        quarticCoreD6F6P9c4f5ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c4f5ABCDEFG810, quarticCoreD6F6P2c4f5ABCDEFG810, quarticCoreD6F6P3c4f5ABCDEFG810, quarticCoreD6F6P4c4f5ABCDEFG810, quarticCoreD6F6P5c4f5ABCDEFG810, quarticCoreD6F6P6c4f5ABCDEFG810, quarticCoreD6F6P7c4f5ABCDEFG810, quarticCoreD6F6P8c4f5ABCDEFG810, quarticCoreD6F6P9c4f5ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c4f6
    (b d : k) :
    quarticCoreD6F6P1c4f6ABCDEFG810 b d +
        quarticCoreD6F6P2c4f6ABCDEFG810 b d +
        quarticCoreD6F6P3c4f6ABCDEFG810 b d +
        quarticCoreD6F6P4c4f6ABCDEFG810 b d +
        quarticCoreD6F6P7c4f6ABCDEFG810 b d +
        quarticCoreD6F6P9c4f6ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c4f6ABCDEFG810, quarticCoreD6F6P2c4f6ABCDEFG810, quarticCoreD6F6P3c4f6ABCDEFG810, quarticCoreD6F6P4c4f6ABCDEFG810, quarticCoreD6F6P7c4f6ABCDEFG810, quarticCoreD6F6P9c4f6ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c5f0
    (b d : k) :
    quarticCoreD6F6P1c5f0ABCDEFG810 b d +
        quarticCoreD6F6P2c5f0ABCDEFG810 b d +
        quarticCoreD6F6P3c5f0ABCDEFG810 b d +
        quarticCoreD6F6P4c5f0ABCDEFG810 b d +
        quarticCoreD6F6P5c5f0ABCDEFG810 b d +
        quarticCoreD6F6P6c5f0ABCDEFG810 b d +
        quarticCoreD6F6P7c5f0ABCDEFG810 b d +
        quarticCoreD6F6P8c5f0ABCDEFG810 b d +
        quarticCoreD6F6P9c5f0ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c5f0ABCDEFG810, quarticCoreD6F6P2c5f0ABCDEFG810, quarticCoreD6F6P3c5f0ABCDEFG810, quarticCoreD6F6P4c5f0ABCDEFG810, quarticCoreD6F6P5c5f0ABCDEFG810, quarticCoreD6F6P6c5f0ABCDEFG810, quarticCoreD6F6P7c5f0ABCDEFG810, quarticCoreD6F6P8c5f0ABCDEFG810, quarticCoreD6F6P9c5f0ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c5f1
    (b d : k) :
    quarticCoreD6F6P1c5f1ABCDEFG810 b d +
        quarticCoreD6F6P2c5f1ABCDEFG810 b d +
        quarticCoreD6F6P3c5f1ABCDEFG810 b d +
        quarticCoreD6F6P4c5f1ABCDEFG810 b d +
        quarticCoreD6F6P5c5f1ABCDEFG810 b d +
        quarticCoreD6F6P6c5f1ABCDEFG810 b d +
        quarticCoreD6F6P7c5f1ABCDEFG810 b d +
        quarticCoreD6F6P8c5f1ABCDEFG810 b d +
        quarticCoreD6F6P9c5f1ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c5f1ABCDEFG810, quarticCoreD6F6P2c5f1ABCDEFG810, quarticCoreD6F6P3c5f1ABCDEFG810, quarticCoreD6F6P4c5f1ABCDEFG810, quarticCoreD6F6P5c5f1ABCDEFG810, quarticCoreD6F6P6c5f1ABCDEFG810, quarticCoreD6F6P7c5f1ABCDEFG810, quarticCoreD6F6P8c5f1ABCDEFG810, quarticCoreD6F6P9c5f1ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c5f2
    (b d : k) :
    quarticCoreD6F6P1c5f2ABCDEFG810 b d +
        quarticCoreD6F6P2c5f2ABCDEFG810 b d +
        quarticCoreD6F6P3c5f2ABCDEFG810 b d +
        quarticCoreD6F6P4c5f2ABCDEFG810 b d +
        quarticCoreD6F6P5c5f2ABCDEFG810 b d +
        quarticCoreD6F6P6c5f2ABCDEFG810 b d +
        quarticCoreD6F6P7c5f2ABCDEFG810 b d +
        quarticCoreD6F6P8c5f2ABCDEFG810 b d +
        quarticCoreD6F6P9c5f2ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c5f2ABCDEFG810, quarticCoreD6F6P2c5f2ABCDEFG810, quarticCoreD6F6P3c5f2ABCDEFG810, quarticCoreD6F6P4c5f2ABCDEFG810, quarticCoreD6F6P5c5f2ABCDEFG810, quarticCoreD6F6P6c5f2ABCDEFG810, quarticCoreD6F6P7c5f2ABCDEFG810, quarticCoreD6F6P8c5f2ABCDEFG810, quarticCoreD6F6P9c5f2ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c5f3
    (b d : k) :
    quarticCoreD6F6P1c5f3ABCDEFG810 b d +
        quarticCoreD6F6P2c5f3ABCDEFG810 b d +
        quarticCoreD6F6P3c5f3ABCDEFG810 b d +
        quarticCoreD6F6P4c5f3ABCDEFG810 b d +
        quarticCoreD6F6P5c5f3ABCDEFG810 b d +
        quarticCoreD6F6P6c5f3ABCDEFG810 b d +
        quarticCoreD6F6P7c5f3ABCDEFG810 b d +
        quarticCoreD6F6P8c5f3ABCDEFG810 b d +
        quarticCoreD6F6P9c5f3ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c5f3ABCDEFG810, quarticCoreD6F6P2c5f3ABCDEFG810, quarticCoreD6F6P3c5f3ABCDEFG810, quarticCoreD6F6P4c5f3ABCDEFG810, quarticCoreD6F6P5c5f3ABCDEFG810, quarticCoreD6F6P6c5f3ABCDEFG810, quarticCoreD6F6P7c5f3ABCDEFG810, quarticCoreD6F6P8c5f3ABCDEFG810, quarticCoreD6F6P9c5f3ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c5f4
    (b d : k) :
    quarticCoreD6F6P1c5f4ABCDEFG810 b d +
        quarticCoreD6F6P2c5f4ABCDEFG810 b d +
        quarticCoreD6F6P3c5f4ABCDEFG810 b d +
        quarticCoreD6F6P4c5f4ABCDEFG810 b d +
        quarticCoreD6F6P5c5f4ABCDEFG810 b d +
        quarticCoreD6F6P6c5f4ABCDEFG810 b d +
        quarticCoreD6F6P7c5f4ABCDEFG810 b d +
        quarticCoreD6F6P8c5f4ABCDEFG810 b d +
        quarticCoreD6F6P9c5f4ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c5f4ABCDEFG810, quarticCoreD6F6P2c5f4ABCDEFG810, quarticCoreD6F6P3c5f4ABCDEFG810, quarticCoreD6F6P4c5f4ABCDEFG810, quarticCoreD6F6P5c5f4ABCDEFG810, quarticCoreD6F6P6c5f4ABCDEFG810, quarticCoreD6F6P7c5f4ABCDEFG810, quarticCoreD6F6P8c5f4ABCDEFG810, quarticCoreD6F6P9c5f4ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c5f5
    (b d : k) :
    quarticCoreD6F6P1c5f5ABCDEFG810 b d +
        quarticCoreD6F6P2c5f5ABCDEFG810 b d +
        quarticCoreD6F6P3c5f5ABCDEFG810 b d +
        quarticCoreD6F6P4c5f5ABCDEFG810 b d +
        quarticCoreD6F6P5c5f5ABCDEFG810 b d +
        quarticCoreD6F6P6c5f5ABCDEFG810 b d +
        quarticCoreD6F6P7c5f5ABCDEFG810 b d +
        quarticCoreD6F6P9c5f5ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c5f5ABCDEFG810, quarticCoreD6F6P2c5f5ABCDEFG810, quarticCoreD6F6P3c5f5ABCDEFG810, quarticCoreD6F6P4c5f5ABCDEFG810, quarticCoreD6F6P5c5f5ABCDEFG810, quarticCoreD6F6P6c5f5ABCDEFG810, quarticCoreD6F6P7c5f5ABCDEFG810, quarticCoreD6F6P9c5f5ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c6f0
    (b d : k) :
    quarticCoreD6F6P1c6f0ABCDEFG810 b d +
        quarticCoreD6F6P2c6f0ABCDEFG810 b d +
        quarticCoreD6F6P3c6f0ABCDEFG810 b d +
        quarticCoreD6F6P4c6f0ABCDEFG810 b d +
        quarticCoreD6F6P5c6f0ABCDEFG810 b d +
        quarticCoreD6F6P6c6f0ABCDEFG810 b d +
        quarticCoreD6F6P7c6f0ABCDEFG810 b d +
        quarticCoreD6F6P8c6f0ABCDEFG810 b d +
        quarticCoreD6F6P9c6f0ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c6f0ABCDEFG810, quarticCoreD6F6P2c6f0ABCDEFG810, quarticCoreD6F6P3c6f0ABCDEFG810, quarticCoreD6F6P4c6f0ABCDEFG810, quarticCoreD6F6P5c6f0ABCDEFG810, quarticCoreD6F6P6c6f0ABCDEFG810, quarticCoreD6F6P7c6f0ABCDEFG810, quarticCoreD6F6P8c6f0ABCDEFG810, quarticCoreD6F6P9c6f0ABCDEFG810]
  try ring

set_option maxHeartbeats 64000000 in
theorem quarticCoreD6F6_combine_c6f1
    (b d : k) :
    quarticCoreD6F6P1c6f1ABCDEFG810 b d +
        quarticCoreD6F6P2c6f1ABCDEFG810 b d +
        quarticCoreD6F6P3c6f1ABCDEFG810 b d +
        quarticCoreD6F6P4c6f1ABCDEFG810 b d +
        quarticCoreD6F6P5c6f1ABCDEFG810 b d +
        quarticCoreD6F6P6c6f1ABCDEFG810 b d +
        quarticCoreD6F6P7c6f1ABCDEFG810 b d +
        quarticCoreD6F6P8c6f1ABCDEFG810 b d +
        quarticCoreD6F6P9c6f1ABCDEFG810 b d =
      (0 : k) := by
  simp only [quarticCoreD6F6P1c6f1ABCDEFG810, quarticCoreD6F6P2c6f1ABCDEFG810, quarticCoreD6F6P3c6f1ABCDEFG810, quarticCoreD6F6P4c6f1ABCDEFG810, quarticCoreD6F6P5c6f1ABCDEFG810, quarticCoreD6F6P6c6f1ABCDEFG810, quarticCoreD6F6P7c6f1ABCDEFG810, quarticCoreD6F6P8c6f1ABCDEFG810, quarticCoreD6F6P9c6f1ABCDEFG810]
  try ring

end QuarticFullConeABCDEFG810D6F6
end Max11DegreeRoutes
end
