import Sol810ThirteenthDefinitionsBlockedDiagScratch

/-! Narrow diagnostics for the two Core-transparency sites used by the
current scale-zero thirteenth-defect repair. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section ScalarCore

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 400000000 in
/-- The exact scalar transparency pattern used before the clearing `ring`:
unfolding the Core and every block transports an already-expanded equality. -/
theorem thirteenthScalarCoreUnfoldSiteDiag810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda rhs : F)
    (hExpanded :
      localClearedFourteenthDefectBlockDiag0_810 h a7 a6 a5 a4 a3 a2 a1 a0
          b8 b7 b6 b5 b4 b3 b2 b1 lambda
        + localClearedFourteenthDefectBlockDiag1_810 h a7 a6 a5 a4 a3 a2 a1 a0
          b8 b7 b6 b5 b4 b3 b2 b1 lambda
        + localClearedFourteenthDefectBlockDiag2_810 h a7 a6 a5 a4 a3 a2 a1 a0
          b8 b7 b6 b5 b4 b3 b2 b1 lambda
        + localClearedFourteenthDefectBlockDiag3_810 h a7 a6 a5 a4 a3 a2 a1 a0
          b8 b7 b6 b5 b4 b3 b2 b1 lambda
        + localClearedFourteenthDefectBlockDiag4_810 h a7 a6 a5 a4 a3 a2 a1 a0
          b8 b7 b6 b5 b4 b3 b2 b1 lambda
        + localClearedFourteenthDefectBlockDiag5_810 h a7 a6 a5 a4 a3 a2 a1 a0
          b8 b7 b6 b5 b4 b3 b2 b1 lambda
        + localClearedFourteenthDefectBlockDiag6_810 h a7 a6 a5 a4 a3 a2 a1 a0
          b8 b7 b6 b5 b4 b3 b2 b1 lambda
        + localClearedFourteenthDefectBlockDiag7_810 h a7 a6 a5 a4 a3 a2 a1 a0
          b8 b7 b6 b5 b4 b3 b2 b1 lambda
        + localClearedFourteenthDefectBlockDiag8_810 h a7 a6 a5 a4 a3 a2 a1 a0
          b8 b7 b6 b5 b4 b3 b2 b1 lambda
        + localClearedFourteenthDefectBlockDiag9_810 h a7 a6 a5 a4 a3 a2 a1 a0
          b8 b7 b6 b5 b4 b3 b2 b1 lambda
        + localClearedFourteenthDefectBlockDiag10_810 h a7 a6 a5 a4 a3 a2 a1 a0
          b8 b7 b6 b5 b4 b3 b2 b1 lambda
        + localClearedFourteenthDefectBlockDiag11_810 h a7 a6 a5 a4 a3 a2 a1 a0
          b8 b7 b6 b5 b4 b3 b2 b1 lambda = rhs) :
      localClearedFourteenthDefectBlockedDiag810 h a7 a6 a5 a4 a3 a2 a1 a0
          b8 b7 b6 b5 b4 b3 b2 b1 lambda = rhs := by
  simpa only [localClearedFourteenthDefectBlockedDiag810,
    localClearedFourteenthDefectBlockDiag0_810,
    localClearedFourteenthDefectBlockDiag1_810,
    localClearedFourteenthDefectBlockDiag2_810,
    localClearedFourteenthDefectBlockDiag3_810,
    localClearedFourteenthDefectBlockDiag4_810,
    localClearedFourteenthDefectBlockDiag5_810,
    localClearedFourteenthDefectBlockDiag6_810,
    localClearedFourteenthDefectBlockDiag7_810,
    localClearedFourteenthDefectBlockDiag8_810,
    localClearedFourteenthDefectBlockDiag9_810,
    localClearedFourteenthDefectBlockDiag10_810,
    localClearedFourteenthDefectBlockDiag11_810] using hExpanded

end ScalarCore

section MappedCore

variable {k : Type*} [Field k] [CharZero k]

def localClearedFourteenthDefectPolyDiag810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (lambda : k) : k[X] :=
  localClearedFourteenthDefectBlockedDiag810 h a7 a6 a5 a4 a3 a2 a1 a0
    b8 b7 b6 b5 b4 b3 b2 b1 (Polynomial.C lambda)

set_option maxHeartbeats 400000000 in
/-- The exact downstream `hclear` shape: after explicitly unfolding the
polynomial wrapper, Core, and blocks, `algebraMap` transports the blocked
numerator to the scalar Core equality. -/
theorem thirteenthHclearCoreMapSimpaSiteDiag810
    (h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (lambda : k) (rhs : RatFunc k)
    (hScalar :
      localClearedFourteenthDefectBlockedDiag810
          (algebraMap k[X] (RatFunc k) h)
          (algebraMap k[X] (RatFunc k) a7)
          (algebraMap k[X] (RatFunc k) a6)
          (algebraMap k[X] (RatFunc k) a5)
          (algebraMap k[X] (RatFunc k) a4)
          (algebraMap k[X] (RatFunc k) a3)
          (algebraMap k[X] (RatFunc k) a2)
          (algebraMap k[X] (RatFunc k) a1)
          (algebraMap k[X] (RatFunc k) a0)
          (algebraMap k[X] (RatFunc k) b8)
          (algebraMap k[X] (RatFunc k) b7)
          (algebraMap k[X] (RatFunc k) b6)
          (algebraMap k[X] (RatFunc k) b5)
          (algebraMap k[X] (RatFunc k) b4)
          (algebraMap k[X] (RatFunc k) b3)
          (algebraMap k[X] (RatFunc k) b2)
          (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda) = rhs) :
      algebraMap k[X] (RatFunc k)
          (localClearedFourteenthDefectPolyDiag810 h a7 a6 a5 a4 a3 a2 a1 a0
            b8 b7 b6 b5 b4 b3 b2 b1 lambda) = rhs := by
  simpa [localClearedFourteenthDefectPolyDiag810,
    localClearedFourteenthDefectBlockedDiag810,
    localClearedFourteenthDefectBlockDiag0_810,
    localClearedFourteenthDefectBlockDiag1_810,
    localClearedFourteenthDefectBlockDiag2_810,
    localClearedFourteenthDefectBlockDiag3_810,
    localClearedFourteenthDefectBlockDiag4_810,
    localClearedFourteenthDefectBlockDiag5_810,
    localClearedFourteenthDefectBlockDiag6_810,
    localClearedFourteenthDefectBlockDiag7_810,
    localClearedFourteenthDefectBlockDiag8_810,
    localClearedFourteenthDefectBlockDiag9_810,
    localClearedFourteenthDefectBlockDiag10_810,
    localClearedFourteenthDefectBlockDiag11_810,
    map_sub, map_mul, map_pow, map_ofNat, map_neg, map_add,
    RatFunc.algebraMap_C] using hScalar

end MappedCore

end Max11DegreeRoutes
