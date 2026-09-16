import Grok610ScaleZeroConeCascadePart101Scratch
import Grok610ScaleZeroConeCascadePart102Scratch

/-! # Scale-zero cone cascade for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroValuationEndgameScratch` on the constant
core `H = (C t)²`.  That file reconstructed the nine triangular Faber
coordinates of the depressed decic and excluded a differentially constant
free core.  This file supplies the missing `(4,10)`-style polynomial
trajectory: the depressed sextic letters `(A, B, C₀, D₀, E₀)` have
literal representatives in `k[x]`, the weight-fifteen primitive of the
integrated trajectory is a polynomial in those letters whose derivative
is the nonzero constant `j / t`, and therefore that primitive has Newton
degree one.

The degree-one identity bounds the free core.  If every letter is a
constant polynomial the primitive is constant, contradicting degree one.
If `A` is the unique highest-degree letter and `L ≠ 0`, the face
`A⁷ L` is unique of degree `7 deg A ≥ 7`.  If `L = 0` and `B` is
nonconstant, `A⁶ B` is unique.  If `L = 0`, `B = 0` and `β ≠ 0`, the
load face `β A⁶` is unique.  If `B` is the unique highest-degree letter
on the extreme cone `3 deg A < 2 deg B` with `L = 0` or `7 deg A < 5 deg B`,
the face `B⁵` is unique.  If `D₀` is the only nonconstant letter, the
face `D₀³` is unique of degree at least three.  If `E₀` is the only
nonconstant letter and `β ≠ 0`, the face `β E₀²` is unique of degree
at least two.

The leaf is not closed.  The residual Newton cone is a nonconstant
polynomial core in which either two or more letters share the maximal
degree, or else `A` uniquely leads with `L = 0` and `B` a (possibly
zero) constant, and in the `B = 0` case also `β = 0`, or else `E₀` is
the unique nonconstant letter with `β = 0`.  The already-constant first
integrals `κ, λ, μ` and the weight-seventy residual `ο` remain available
and are not consumed.  No total-degree or twice-prime theorem is used.
No finite-root shortcut is used.
-/
/-! ## Degree bookkeeping -/

namespace Max11DegreeRoutes

#print axioms natDegree_eq_one_of_derivative_eq_nonzero_C610
#print axioms smul_add_lower_ne_C610
#print axioms UniqueHighACone610
#print axioms UniqueHighBCone610
#print axioms ExtremeHighBCone610
#print axioms degreeZeroBaseGroupPolynomial610
#print axioms degreeZeroPrimitivePolynomial610
#print axioms degreeZeroIntegratedPrimitive610
#print axioms degreeZeroPrimitive610_eq_integratedPrimitive
#print axioms algebraMap_degreeZeroPrimitivePolynomial610
#print axioms constantScale_monicSextic_polynomialCore610
#print axioms normalized610ScaleZero_exists_primitivePolynomial
#print axioms degreeZeroPrimitivePolynomial610_false_of_constant_core
#print axioms uniqueHighA_impossible_of_l_ne610
#print axioms uniqueHighA_impossible_of_l_zero_B_pos610
#print axioms uniqueHighA_impossible_of_l_zero_B_zero_beta_ne
#print axioms extremeHighB_impossible
#print axioms uniqueNonconstantD0_impossible
#print axioms uniqueNonconstantB_impossible
#print axioms uniqueNonconstantE0_impossible_of_beta_ne
#print axioms normalized610ScaleZero_coneCascadeResidual

end Max11DegreeRoutes
