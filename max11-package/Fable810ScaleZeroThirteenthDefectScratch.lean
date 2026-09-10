import Fable810ScaleZeroThirteenthDefectPart37Scratch

/-! # Scale-zero thirteenth defect for the normalized `(8,10)`, `H = 0` leaf

The twelfth-defect packet already makes the discriminator `N` a
ground-field constant and, after a square root of the core, clears the
first twelve octic/decic defects to ground constants times `h¹⁴`, `h²¹`,
`h²⁸`, `h³⁵`, `h⁴²`, `h⁴⁹`, `h⁵⁶`, `h⁶³`, `h⁷⁰`, `h⁷⁷`, `h⁸⁴`, and
`h⁹¹`.  This file consumes the next unused Keller coefficient of the
same monic octic-decic depression: the degree-`3` Jacobian row is
`4 T G' + 3 U F' + 2 V E' + W D'
- F U' - 2 E V' - 3 D W' - 4 C X' = 0`.  Its first integral needs the
degree-`5` and degree-`6` rows a second time, with multipliers
`-(1/16) A` and `-(1/16) B`, and the corresponding fourteenth cleared
polynomial defect of weight ninety-eight is likewise a ground-field
constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  The same zero/nonzero split is recorded
for the weight-`98` defect itself.  Root-evaluation from a scale-two
face is unavailable, because a nonzero constant has no finite root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`2` residual of
the same monic depression.
-/

/-! This module is now a pure import aggregator: its declarations live in the
chained `Part..` modules above, one per file, so that no single module elaborates
them all at once.  Every statement, name, binder and section context is unchanged. -/

namespace Max11DegreeRoutes

#print axioms fableScaleZero_fourteenthCoefficientJacobianRow_raw_810
#print axioms scaleZero_fourteenthCoefficientJacobianRow_810
#print axioms normalized810ScaleZero_fourteenthCoefficientJacobianRow
#print axioms normalized810ScaleZero_fourteenthCoefficientJacobianRow_collapsed
#print axioms differentialJacobian_coeff_3_monicOcticDecic
#print axioms scaleZero_monicOcticDecic_degree3Row_810
#print axioms xiResidual810_deriv_zero
#print axioms scaleZero_xiResidual_deriv_zero_810
#print axioms fourteenthDefect_eq_clearedXi810
#print axioms nonzeroFace810_fourteenthDefectPowerRelation
#print axioms scaleZero_thirteenthClearedDefect_exists_C_810
#print axioms scaleZero_alignedThirteenthClearedDefect_exists_C_810
#print axioms scaleZero_nonzeroThirteenthClearedDefect_exists_C_810
#print axioms normalized810ScaleZero_exists_thirteenthClearedDefect
#print axioms normalized810ScaleZero_thirteenthClearedDefect_exists_C
#print axioms normalized810ScaleZero_thirteenthClearedDefect_natDegree_le_zero
#print axioms normalized810ScaleZero_thirteenthClearedDefectFirstFace
#print axioms normalized810ScaleZero_thirteenthClearedDefectBranches
#print axioms normalized810ScaleZero_aligned_exists_thirteenthClearedDefect
#print axioms normalized810ScaleZero_nonzero_exists_thirteenthClearedDefect


end Max11DegreeRoutes
