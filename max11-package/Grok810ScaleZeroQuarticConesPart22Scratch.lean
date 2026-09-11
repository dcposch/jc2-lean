import Grok810ScaleZeroQuarticConesPart01Scratch
import Grok810ScaleZeroQuarticConesPart03Scratch
import Grok810ScaleZeroQuarticConesPart04Scratch
import Grok810ScaleZeroQuarticConesPart05Scratch

/-! # Part 22 of `Grok810ScaleZeroQuarticConesScratch`.

One declaration split out of `Grok810ScaleZeroQuarticConesScratch`; statements are byte-identical.
-/

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

section QuarticExhaust810

variable {k : Type*} [Field k] [CharZero k]

theorem quarticScore_eq_lt_GEC {nG nE nC : ℕ}
    (hxy : 6 * nG = 8 * nE) (hyz : 4 * nE < 6 * nC) :
    4 * nG < 8 * nC := by omega

theorem quarticScore_lt_trans_GED {nG nE nD : ℕ}
    (hxy : 6 * nG < 8 * nE) (hyz : 5 * nE < 6 * nD) :
    5 * nG < 8 * nD := by omega

theorem quarticScore_eq_lt_GED {nG nE nD : ℕ}
    (hxy : 6 * nG = 8 * nE) (hyz : 5 * nE < 6 * nD) :
    5 * nG < 8 * nD := by omega

theorem quarticScore_lt_trans_GEF {nG nE nF : ℕ}
    (hxy : 6 * nG < 8 * nE) (hyz : 7 * nE < 6 * nF) :
    7 * nG < 8 * nF := by omega

theorem quarticScore_eq_lt_GEF {nG nE nF : ℕ}
    (hxy : 6 * nG = 8 * nE) (hyz : 7 * nE < 6 * nF) :
    7 * nG < 8 * nF := by omega

theorem quarticScore_lt_trans_GFA {nG nF nA : ℕ}
    (hxy : 7 * nG < 8 * nF) (hyz : 2 * nF < 7 * nA) :
    2 * nG < 8 * nA := by omega

theorem quarticScore_eq_lt_GFA {nG nF nA : ℕ}
    (hxy : 7 * nG = 8 * nF) (hyz : 2 * nF < 7 * nA) :
    2 * nG < 8 * nA := by omega

theorem quarticScore_lt_trans_GFB {nG nF nB : ℕ}
    (hxy : 7 * nG < 8 * nF) (hyz : 3 * nF < 7 * nB) :
    3 * nG < 8 * nB := by omega

theorem quarticScore_eq_lt_GFB {nG nF nB : ℕ}
    (hxy : 7 * nG = 8 * nF) (hyz : 3 * nF < 7 * nB) :
    3 * nG < 8 * nB := by omega

theorem quarticScore_lt_trans_GFC {nG nF nC : ℕ}
    (hxy : 7 * nG < 8 * nF) (hyz : 4 * nF < 7 * nC) :
    4 * nG < 8 * nC := by omega

theorem quarticScore_eq_lt_GFC {nG nF nC : ℕ}
    (hxy : 7 * nG = 8 * nF) (hyz : 4 * nF < 7 * nC) :
    4 * nG < 8 * nC := by omega

theorem quarticScore_lt_trans_GFD {nG nF nD : ℕ}
    (hxy : 7 * nG < 8 * nF) (hyz : 5 * nF < 7 * nD) :
    5 * nG < 8 * nD := by omega

theorem quarticScore_eq_lt_GFD {nG nF nD : ℕ}
    (hxy : 7 * nG = 8 * nF) (hyz : 5 * nF < 7 * nD) :
    5 * nG < 8 * nD := by omega

theorem quarticScore_lt_trans_GFE {nG nF nE : ℕ}
    (hxy : 7 * nG < 8 * nF) (hyz : 6 * nF < 7 * nE) :
    6 * nG < 8 * nE := by omega

theorem quarticScore_eq_lt_GFE {nG nF nE : ℕ}
    (hxy : 7 * nG = 8 * nF) (hyz : 6 * nF < 7 * nE) :
    6 * nG < 8 * nE := by omega

/-! Named tournament fragments (post-order). -/

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_A
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB0 : B.natDegree = 0)
    (hC0 : C.natDegree = 0)
    (hD0 : D.natDegree = 0)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  refine QuarticSupportCone810.coneA ?_
  refine ⟨hA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_B
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB : 0 < B.natDegree)
    (hC0 : C.natDegree = 0)
    (hD0 : D.natDegree = 0)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  refine QuarticSupportCone810.coneB ?_
  refine ⟨hB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_FB_of_zero hF0 hB, quarticCmp_GB_of_zero hG0 hB⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_C
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB0 : B.natDegree = 0)
    (hC : 0 < C.natDegree)
    (hD0 : D.natDegree = 0)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  refine QuarticSupportCone810.coneC ?_
  refine ⟨hC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_zero hG0 hC⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_D
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB0 : B.natDegree = 0)
    (hC0 : C.natDegree = 0)
    (hD : 0 < D.natDegree)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  refine QuarticSupportCone810.coneD ?_
  refine ⟨hD, quarticCmp_AD_of_zero hA0 hD, quarticCmp_BD_of_zero hB0 hD, quarticCmp_CD_of_zero hC0 hD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_FD_of_zero hF0 hD, quarticCmp_GD_of_zero hG0 hD⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_E
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB0 : B.natDegree = 0)
    (hC0 : C.natDegree = 0)
    (hD0 : D.natDegree = 0)
    (hE : 0 < E.natDegree)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  refine QuarticSupportCone810.coneE ?_
  refine ⟨hE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_zero hC0 hE, quarticCmp_DE_of_zero hD0 hE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_F
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB0 : B.natDegree = 0)
    (hC0 : C.natDegree = 0)
    (hD0 : D.natDegree = 0)
    (hE0 : E.natDegree = 0)
    (hF : 0 < F.natDegree)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  refine QuarticSupportCone810.coneF ?_
  refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, quarticCmp_BF_of_zero hB0 hF, quarticCmp_CF_of_zero hC0 hF, quarticCmp_DF_of_zero hD0 hF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_G
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB0 : B.natDegree = 0)
    (hC0 : C.natDegree = 0)
    (hD0 : D.natDegree = 0)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG : 0 < G.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  refine QuarticSupportCone810.coneG ?_
  refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_zero hC0 hG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_AB
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB : 0 < B.natDegree)
    (hC0 : C.natDegree = 0)
    (hD0 : D.natDegree = 0)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hABlt : 3 * A.natDegree < 2 * B.natDegree
  · -- B strictly outranks A
    have hRaw_AB : 3 * A.natDegree < 2 * B.natDegree := hABlt
    refine QuarticSupportCone810.coneB ?_
    refine ⟨hB, hRaw_AB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_FB_of_zero hF0 hB, quarticCmp_GB_of_zero hG0 hB⟩
  · by_cases hABeq : 3 * A.natDegree = 2 * B.natDegree
    · -- B ties A
      have hEqRaw_BA : 2 * B.natDegree = 3 * A.natDegree := hABeq.symm
      refine QuarticSupportCone810.coneAB ?_
      refine ⟨hA, hB, hEqRaw_BA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩
    · -- A strictly outranks B
      have hRed_BA : 2 * B.natDegree < 3 * A.natDegree := quarticScore_not_lt_not_eq hABlt hABeq
      have hRaw_BA : 2 * B.natDegree < 3 * A.natDegree := hRed_BA
      refine QuarticSupportCone810.coneA ?_
      refine ⟨hA, hRaw_BA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_AC
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB0 : B.natDegree = 0)
    (hC : 0 < C.natDegree)
    (hD0 : D.natDegree = 0)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hAClt : 2 * A.natDegree < C.natDegree
  · -- C strictly outranks A
    have hRaw_AC : 4 * A.natDegree < 2 * C.natDegree := quarticCmp_AC_to_raw hAClt
    refine QuarticSupportCone810.coneC ?_
    refine ⟨hC, quarticCmp_AC_of_raw hRaw_AC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_zero hG0 hC⟩
  · by_cases hACeq : 2 * A.natDegree = C.natDegree
    · -- C ties A
      have hEqRaw_CA : 2 * C.natDegree = 4 * A.natDegree := quarticEq_CA_to_raw (hACeq.symm)
      refine QuarticSupportCone810.coneAC ?_
      refine ⟨hA, hC, quarticEq_CA_of_raw hEqRaw_CA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩
    · -- A strictly outranks C
      have hRed_CA : C.natDegree < 2 * A.natDegree := quarticScore_not_lt_not_eq hAClt hACeq
      have hRaw_CA : 2 * C.natDegree < 4 * A.natDegree := quarticCmp_CA_to_raw hRed_CA
      refine QuarticSupportCone810.coneA ?_
      refine ⟨hA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_raw hRaw_CA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩

end QuarticExhaust810

end Max11DegreeRoutes
