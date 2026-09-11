import Sol610ScaleTwoDegreeZeroPrimitivePart101Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart18Scratch
import Sol610ScaleTwoDegreeZeroPrimitivePart19Scratch

/-! # Exact primitive for the `(6,10)` degree-zero row

The last Jacobian row is inhomogeneous, so this weight-fifteen primitive is
not a first integral.  Its derivative is the literal row zero, modulo the
already established residual tower.  The grouped formula and differential
certificate were independently reconstructed by
`derive_610_degree_zero_residual.py` (SHA256
`cd333da32d89eb7eb86f0fc1043ee718f65716faa41edcf29bc4ca2248473b58`).
-/

namespace Max11DegreeRoutes

#print axioms degreeZeroPrimitive610_deriv_identity
#print axioms degreeZeroPrimitive610_deriv_eq_row

end Max11DegreeRoutes
