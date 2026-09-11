import Sol610ScaleTwoAlignedTwelfthCertificateWithCPart101Scratch
import Sol610ScaleTwoAlignedTwelfthCertificateWithCPart12Scratch

/-! # Actual degree-three multiplier certificate with the consumed C row

The frozen weight-thirty candidate necessarily sees `b8'`, while the literal
degree-three Jacobian row and defects `D,...,Lambda` do not.  The minimal
source-backed repair is the already-consumed base equation

`C = 9 b8 H - 15 a4 H^3 - 5 a5^2 - kappa H^5 = 0`

together with its weight-five derivative row.  Exact CAS elimination gives
the certificate below.  All rational cofactors were cleared by `16384`; the
identity is therefore valid over every characteristic-zero field without
polynomial division.
-/

namespace Max11DegreeRoutes

#print axioms alignedTwelfthDefect_withC_multiplier_identity_610

end Max11DegreeRoutes
