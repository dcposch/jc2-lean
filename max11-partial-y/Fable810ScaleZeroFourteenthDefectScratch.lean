import Fable810ScaleZeroFourteenthDefectPart103Scratch

/-! # Scale-zero fourteenth defect for the normalized `(8,10)`, `H = 0` leaf

The thirteenth-defect packet already makes the discriminator `N` a
ground-field constant and, after a square root of the core, clears the
first thirteen octic/decic defects to ground constants times `h¹⁴`,
`h²¹`, `h²⁸`, `h³⁵`, `h⁴²`, `h⁴⁹`, `h⁵⁶`, `h⁶³`, `h⁷⁰`, `h⁷⁷`, `h⁸⁴`,
`h⁹¹`, and `h⁹⁸`.  This file consumes the next unused Keller coefficient
of the same monic octic-decic depression: the degree-`2` Jacobian row is
`3 U G' + 2 V F' + W E' - F V' - 2 E W' - 3 D X' = 0`.  Its first
integral needs the degree-`4`, degree-`5`, and degree-`6` rows a second
time, with multipliers `-(3/64) A`, `-(3/64) B`, and
`(33/1024) A² - (3/64) C`, and the corresponding fifteenth cleared
polynomial defect of weight one hundred five is likewise a ground-field
constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  The same zero/nonzero split is recorded
for the weight-`105` defect itself.  Root-evaluation from a scale-two
face is unavailable, because a nonzero constant has no finite root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`1` residual of
the same monic depression.
-/

/-! This module is now a pure import aggregator: its declarations live in the
chained `Part..` modules above, one per file, so that no single module elaborates
them all at once.  Every statement, name, binder and section context is unchanged. -/

namespace Max11DegreeRoutes

#print axioms fableScaleZero_fifteenthCoefficientJacobianRow_raw_810
#print axioms scaleZero_fifteenthCoefficientJacobianRow_810
#print axioms normalized810ScaleZero_fifteenthCoefficientJacobianRow
#print axioms normalized810ScaleZero_fifteenthCoefficientJacobianRow_collapsed
#print axioms differentialJacobian_coeff_2_monicOcticDecic
#print axioms scaleZero_monicOcticDecic_degree2Row_810
#print axioms omicronResidual810_deriv_zero
#print axioms scaleZero_omicronResidual_deriv_zero_810
#print axioms fifteenthDefect_eq_clearedOmicron810
#print axioms nonzeroFace810_fifteenthDefectPowerRelation
#print axioms scaleZero_fourteenthClearedDefect_exists_C_810
#print axioms scaleZero_alignedFourteenthClearedDefect_exists_C_810
#print axioms scaleZero_nonzeroFourteenthClearedDefect_exists_C_810
#print axioms normalized810ScaleZero_exists_fourteenthClearedDefect
#print axioms normalized810ScaleZero_fourteenthClearedDefect_exists_C
#print axioms normalized810ScaleZero_fourteenthClearedDefect_natDegree_le_zero
#print axioms normalized810ScaleZero_fourteenthClearedDefectFirstFace
#print axioms normalized810ScaleZero_fourteenthClearedDefectBranches
#print axioms normalized810ScaleZero_aligned_exists_fourteenthClearedDefect
#print axioms normalized810ScaleZero_nonzero_exists_fourteenthClearedDefect


end Max11DegreeRoutes
