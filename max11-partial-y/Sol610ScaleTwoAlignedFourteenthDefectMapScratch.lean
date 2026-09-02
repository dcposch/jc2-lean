import Sol610ScaleTwoAlignedFourteenthDefectClearingScratch

/-! # Ring-hom transport for the compact aligned `(6,10)` ν numerator -/

noncomputable section

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section FourteenthDefectMap610

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 400000000 in
/-- The compact source numerator commutes with every commutative-ring
homomorphism.  Keeping this transport modular prevents the 72-term expression
from being re-expanded in every later RatFunc descent. -/
theorem map_alignedClearedFourteenthDefect610
    (phi : R →+* S)
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : R) :
    phi (alignedClearedFourteenthDefect610 h a5 a4 a3 a2 a1 a0 b8 b7 b6
      b5 b4 b3 b2 b1) =
      alignedClearedFourteenthDefect610 (phi h) (phi a5) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi b8) (phi b7) (phi b6) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) := by
  simp only [alignedClearedFourteenthDefect610,
    clearedFourteenthResidual610, map_sub, map_add, map_mul, map_pow,
    map_neg, map_ofNat]

#print axioms map_alignedClearedFourteenthDefect610

end FourteenthDefectMap610

end Max11DegreeRoutes
