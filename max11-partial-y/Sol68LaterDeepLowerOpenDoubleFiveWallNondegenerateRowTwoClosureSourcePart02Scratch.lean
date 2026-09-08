import Sol68LaterDeepLowerOpenDoubleFiveWallNondegenerateRowTwoClosureSourcePart01Scratch

/-! # Row-two closure of the nondegenerate double-five tangent -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallNondegenerateRowTwoClosureSource68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem laterDeepLowerOpenDoubleFiveWall_nondegenerate_rowTwo_inconsistent68
    (N a b c d e delta : k) (hN : N ≠ 0) (ha : a ≠ 0)
    (hc : c ≠ 0) (hdisc : a * b ^ 2 = c ^ 2)
    (packet : LaterDeepLowerOpenDoubleFiveWallScalarPacket68
      N a b c d e delta)
    (hrowTwo : (8 / 27 : k) * N *
        (a * b ^ 3 + 9 * a * b * e + 9 * a * c * d - 18 * b * c ^ 2) +
      (2 / 3 : k) * N * delta * a ^ 3 = 0) : False := by
  have hb : b ≠ 0 := by
    intro hb0
    rw [hb0, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hdisc
    exact hc (eq_zero_of_pow_eq_zero hdisc.symm)
  have hcd : a * c * d + a * b ^ 3 - 3 * a * b * e = 0 := by
    have hp : b * (a * c * d + a * b ^ 3 - 3 * a * b * e) = 0 := by
      linear_combination
        -c * packet.three + b ^ 2 * hdisc - 3 * e * hdisc
    exact (mul_eq_zero.mp hp).resolve_left hb
  have hfour : (16 / 27 : k) * b * (-5 * b ^ 2 + 18 * e) +
      (1 / 4 : k) * delta * a ^ 2 = 0 := by
    have hp : a * ((16 / 27 : k) * b * (-5 * b ^ 2 + 18 * e) +
        (1 / 4 : k) * delta * a ^ 2) = 0 := by
      linear_combination a * packet.four - (8 / 3 : k) * hcd
    exact (mul_eq_zero.mp hp).resolve_left ha
  have htwo : (16 / 27 : k) * N * a * b * (-13 * b ^ 2 + 18 * e) +
      (2 / 3 : k) * N * delta * a ^ 3 = 0 := by
    linear_combination
      hrowTwo - (8 / 3 : k) * N * hcd -
        (16 / 3 : k) * N * b * hdisc
  have heprod : N * a * b * (b ^ 2 - 90 * e) = 0 := by
    linear_combination
      (81 / 16 : k) * (htwo - (8 / 3 : k) * N * a * hfour)
  have hNab : N * a * b ≠ 0 := mul_ne_zero (mul_ne_zero hN ha) hb
  have heq : e = (1 / 90 : k) * b ^ 2 := by
    have ht := (mul_eq_zero.mp heprod).resolve_left hNab
    linear_combination (-1 / 90 : k) * ht
  have hdelta : delta * a ^ 2 = (512 / 45 : k) * b ^ 3 := by
    rw [heq] at hfour
    linear_combination 4 * hfour
  have hzero : (8 / 27 : k) * N * a *
        (2 * a * b ^ 3 - 4 * a * b * e) +
      (1 / 9 : k) * N * delta * a ^ 4 = 0 := by
    linear_combination
      packet.rowZero + (8 / 27 : k) * N * a * hcd +
        (8 / 27 : k) * N * a * b * hdisc
  rw [heq] at hzero
  have hbad : (448 / 243 : k) * N * a ^ 2 * b ^ 3 = 0 := by
    linear_combination hzero - (1 / 9 : k) * N * a ^ 2 * hdelta
  have hbadne : (448 / 243 : k) * N * a ^ 2 * b ^ 3 ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hN) (pow_ne_zero 2 ha))
      (pow_ne_zero 3 hb)
  exact hbadne hbad

end LaterDeepLowerOpenDoubleFiveWallNondegenerateRowTwoClosureSource68
end Max11DegreeRoutes
