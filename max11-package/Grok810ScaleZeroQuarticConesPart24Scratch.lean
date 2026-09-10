import Grok810ScaleZeroQuarticConesPart23Scratch

/-! # Part 24 of `Grok810ScaleZeroQuarticConesScratch`.

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

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_ACD
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB0 : B.natDegree = 0)
    (hC : 0 < C.natDegree)
    (hD : 0 < D.natDegree)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hAClt : 2 * A.natDegree < C.natDegree
  · -- C strictly outranks A
    have hRaw_AC : 4 * A.natDegree < 2 * C.natDegree := quarticCmp_AC_to_raw hAClt
    by_cases hCDlt : 5 * C.natDegree < 4 * D.natDegree
    · -- D strictly outranks C
      have hRaw_CD : 5 * C.natDegree < 4 * D.natDegree := hCDlt
      have hRaw_AD : 5 * A.natDegree < 2 * D.natDegree := quarticScore_lt_trans_ACD hRaw_AC hRaw_CD
      refine QuarticSupportCone810.coneD ?_
      refine ⟨hD, hRaw_AD, quarticCmp_BD_of_zero hB0 hD, hRaw_CD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_FD_of_zero hF0 hD, quarticCmp_GD_of_zero hG0 hD⟩
    · by_cases hCDeq : 5 * C.natDegree = 4 * D.natDegree
      · -- D ties C
        have hEqRaw_DC : 4 * D.natDegree = 5 * C.natDegree := hCDeq.symm
        refine QuarticSupportCone810.coneCD ?_
        refine ⟨hC, hD, hEqRaw_DC, quarticCmp_AC_of_raw hRaw_AC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_zero hG0 hC⟩
      · -- C strictly outranks D
        have hRed_DC : 4 * D.natDegree < 5 * C.natDegree := quarticScore_not_lt_not_eq hCDlt hCDeq
        have hRaw_DC : 4 * D.natDegree < 5 * C.natDegree := hRed_DC
        refine QuarticSupportCone810.coneC ?_
        refine ⟨hC, quarticCmp_AC_of_raw hRaw_AC, quarticCmp_BC_of_zero hB0 hC, hRaw_DC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_zero hG0 hC⟩
  · by_cases hACeq : 2 * A.natDegree = C.natDegree
    · -- C ties A
      have hEqRaw_CA : 2 * C.natDegree = 4 * A.natDegree := quarticEq_CA_to_raw (hACeq.symm)
      by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
      · -- D strictly outranks AC
        have hRaw_AD : 5 * A.natDegree < 2 * D.natDegree := hADlt
        have hRaw_CD : 5 * C.natDegree < 4 * D.natDegree := quarticScore_eq_lt_CAD hEqRaw_CA hRaw_AD
        refine QuarticSupportCone810.coneD ?_
        refine ⟨hD, hRaw_AD, quarticCmp_BD_of_zero hB0 hD, hRaw_CD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_FD_of_zero hF0 hD, quarticCmp_GD_of_zero hG0 hD⟩
      · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
        · -- D ties AC
          have hEqRaw_DA : 2 * D.natDegree = 5 * A.natDegree := hADeq.symm
          refine QuarticSupportCone810.coneACD ?_
          refine ⟨hA, hC, hD, quarticEq_CA_of_raw hEqRaw_CA, hEqRaw_DA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩
        · -- AC strictly outranks D
          have hRed_DA : 2 * D.natDegree < 5 * A.natDegree := quarticScore_not_lt_not_eq hADlt hADeq
          have hRaw_DA : 2 * D.natDegree < 5 * A.natDegree := hRed_DA
          refine QuarticSupportCone810.coneAC ?_
          refine ⟨hA, hC, quarticEq_CA_of_raw hEqRaw_CA, quarticCmp_BA_of_zero hB0 hA, hRaw_DA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩
    · -- A strictly outranks C
      have hRed_CA : C.natDegree < 2 * A.natDegree := quarticScore_not_lt_not_eq hAClt hACeq
      have hRaw_CA : 2 * C.natDegree < 4 * A.natDegree := quarticCmp_CA_to_raw hRed_CA
      by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
      · -- D strictly outranks A
        have hRaw_AD : 5 * A.natDegree < 2 * D.natDegree := hADlt
        have hRaw_CD : 5 * C.natDegree < 4 * D.natDegree := quarticScore_lt_trans_CAD hRaw_CA hRaw_AD
        refine QuarticSupportCone810.coneD ?_
        refine ⟨hD, hRaw_AD, quarticCmp_BD_of_zero hB0 hD, hRaw_CD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_FD_of_zero hF0 hD, quarticCmp_GD_of_zero hG0 hD⟩
      · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
        · -- D ties A
          have hEqRaw_DA : 2 * D.natDegree = 5 * A.natDegree := hADeq.symm
          refine QuarticSupportCone810.coneAD ?_
          refine ⟨hA, hD, hEqRaw_DA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_raw hRaw_CA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩
        · -- A strictly outranks D
          have hRed_DA : 2 * D.natDegree < 5 * A.natDegree := quarticScore_not_lt_not_eq hADlt hADeq
          have hRaw_DA : 2 * D.natDegree < 5 * A.natDegree := hRed_DA
          refine QuarticSupportCone810.coneA ?_
          refine ⟨hA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_raw hRaw_CA, hRaw_DA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_ACE
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB0 : B.natDegree = 0)
    (hC : 0 < C.natDegree)
    (hD0 : D.natDegree = 0)
    (hE : 0 < E.natDegree)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hAClt : 2 * A.natDegree < C.natDegree
  · -- C strictly outranks A
    have hRaw_AC : 4 * A.natDegree < 2 * C.natDegree := quarticCmp_AC_to_raw hAClt
    by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
    · -- E strictly outranks C
      have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticCmp_CE_to_raw hCElt
      have hRaw_AE : 6 * A.natDegree < 2 * E.natDegree := quarticScore_lt_trans_ACE hRaw_AC hRaw_CE
      refine QuarticSupportCone810.coneE ?_
      refine ⟨hE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_raw hRaw_CE, quarticCmp_DE_of_zero hD0 hE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
    · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
      · -- E ties C
        have hEqRaw_EC : 4 * E.natDegree = 6 * C.natDegree := quarticEq_EC_to_raw (hCEeq.symm)
        refine QuarticSupportCone810.coneCE ?_
        refine ⟨hC, hE, quarticEq_EC_of_raw hEqRaw_EC, quarticCmp_AC_of_raw hRaw_AC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_zero hG0 hC⟩
      · -- C strictly outranks E
        have hRed_EC : 2 * E.natDegree < 3 * C.natDegree := quarticScore_not_lt_not_eq hCElt hCEeq
        have hRaw_EC : 4 * E.natDegree < 6 * C.natDegree := quarticCmp_EC_to_raw hRed_EC
        refine QuarticSupportCone810.coneC ?_
        refine ⟨hC, quarticCmp_AC_of_raw hRaw_AC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_EC_of_raw hRaw_EC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_zero hG0 hC⟩
  · by_cases hACeq : 2 * A.natDegree = C.natDegree
    · -- C ties A
      have hEqRaw_CA : 2 * C.natDegree = 4 * A.natDegree := quarticEq_CA_to_raw (hACeq.symm)
      by_cases hAElt : 3 * A.natDegree < E.natDegree
      · -- E strictly outranks AC
        have hRaw_AE : 6 * A.natDegree < 2 * E.natDegree := quarticCmp_AE_to_raw hAElt
        have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticScore_eq_lt_CAE hEqRaw_CA hRaw_AE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_raw hRaw_CE, quarticCmp_DE_of_zero hD0 hE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
      · by_cases hAEeq : 3 * A.natDegree = E.natDegree
        · -- E ties AC
          have hEqRaw_EA : 2 * E.natDegree = 6 * A.natDegree := quarticEq_EA_to_raw (hAEeq.symm)
          refine QuarticSupportCone810.coneACE ?_
          refine ⟨hA, hC, hE, quarticEq_CA_of_raw hEqRaw_CA, quarticEq_EA_of_raw hEqRaw_EA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩
        · -- AC strictly outranks E
          have hRed_EA : E.natDegree < 3 * A.natDegree := quarticScore_not_lt_not_eq hAElt hAEeq
          have hRaw_EA : 2 * E.natDegree < 6 * A.natDegree := quarticCmp_EA_to_raw hRed_EA
          refine QuarticSupportCone810.coneAC ?_
          refine ⟨hA, hC, quarticEq_CA_of_raw hEqRaw_CA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_raw hRaw_EA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩
    · -- A strictly outranks C
      have hRed_CA : C.natDegree < 2 * A.natDegree := quarticScore_not_lt_not_eq hAClt hACeq
      have hRaw_CA : 2 * C.natDegree < 4 * A.natDegree := quarticCmp_CA_to_raw hRed_CA
      by_cases hAElt : 3 * A.natDegree < E.natDegree
      · -- E strictly outranks A
        have hRaw_AE : 6 * A.natDegree < 2 * E.natDegree := quarticCmp_AE_to_raw hAElt
        have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticScore_lt_trans_CAE hRaw_CA hRaw_AE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_raw hRaw_CE, quarticCmp_DE_of_zero hD0 hE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
      · by_cases hAEeq : 3 * A.natDegree = E.natDegree
        · -- E ties A
          have hEqRaw_EA : 2 * E.natDegree = 6 * A.natDegree := quarticEq_EA_to_raw (hAEeq.symm)
          refine QuarticSupportCone810.coneAE ?_
          refine ⟨hA, hE, quarticEq_EA_of_raw hEqRaw_EA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_raw hRaw_CA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩
        · -- A strictly outranks E
          have hRed_EA : E.natDegree < 3 * A.natDegree := quarticScore_not_lt_not_eq hAElt hAEeq
          have hRaw_EA : 2 * E.natDegree < 6 * A.natDegree := quarticCmp_EA_to_raw hRed_EA
          refine QuarticSupportCone810.coneA ?_
          refine ⟨hA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_raw hRaw_CA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_raw hRaw_EA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_ACF
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB0 : B.natDegree = 0)
    (hC : 0 < C.natDegree)
    (hD0 : D.natDegree = 0)
    (hE0 : E.natDegree = 0)
    (hF : 0 < F.natDegree)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hAClt : 2 * A.natDegree < C.natDegree
  · -- C strictly outranks A
    have hRaw_AC : 4 * A.natDegree < 2 * C.natDegree := quarticCmp_AC_to_raw hAClt
    by_cases hCFlt : 7 * C.natDegree < 4 * F.natDegree
    · -- F strictly outranks C
      have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := hCFlt
      have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := quarticScore_lt_trans_ACF hRaw_AC hRaw_CF
      refine QuarticSupportCone810.coneF ?_
      refine ⟨hF, hRaw_AF, quarticCmp_BF_of_zero hB0 hF, hRaw_CF, quarticCmp_DF_of_zero hD0 hF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
    · by_cases hCFeq : 7 * C.natDegree = 4 * F.natDegree
      · -- F ties C
        have hEqRaw_FC : 4 * F.natDegree = 7 * C.natDegree := hCFeq.symm
        refine QuarticSupportCone810.coneCF ?_
        refine ⟨hC, hF, hEqRaw_FC, quarticCmp_AC_of_raw hRaw_AC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_GC_of_zero hG0 hC⟩
      · -- C strictly outranks F
        have hRed_FC : 4 * F.natDegree < 7 * C.natDegree := quarticScore_not_lt_not_eq hCFlt hCFeq
        have hRaw_FC : 4 * F.natDegree < 7 * C.natDegree := hRed_FC
        refine QuarticSupportCone810.coneC ?_
        refine ⟨hC, quarticCmp_AC_of_raw hRaw_AC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_EC_of_zero hE0 hC, hRaw_FC, quarticCmp_GC_of_zero hG0 hC⟩
  · by_cases hACeq : 2 * A.natDegree = C.natDegree
    · -- C ties A
      have hEqRaw_CA : 2 * C.natDegree = 4 * A.natDegree := quarticEq_CA_to_raw (hACeq.symm)
      by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
      · -- F strictly outranks AC
        have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
        have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_eq_lt_CAF hEqRaw_CA hRaw_AF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, hRaw_AF, quarticCmp_BF_of_zero hB0 hF, hRaw_CF, quarticCmp_DF_of_zero hD0 hF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
        · -- F ties AC
          have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
          refine QuarticSupportCone810.coneACF ?_
          refine ⟨hA, hC, hF, quarticEq_CA_of_raw hEqRaw_CA, hEqRaw_FA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_GA_of_zero hG0 hA⟩
        · -- AC strictly outranks F
          have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
          have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
          refine QuarticSupportCone810.coneAC ?_
          refine ⟨hA, hC, quarticEq_CA_of_raw hEqRaw_CA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, hRaw_FA, quarticCmp_GA_of_zero hG0 hA⟩
    · -- A strictly outranks C
      have hRed_CA : C.natDegree < 2 * A.natDegree := quarticScore_not_lt_not_eq hAClt hACeq
      have hRaw_CA : 2 * C.natDegree < 4 * A.natDegree := quarticCmp_CA_to_raw hRed_CA
      by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
      · -- F strictly outranks A
        have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
        have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CAF hRaw_CA hRaw_AF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, hRaw_AF, quarticCmp_BF_of_zero hB0 hF, hRaw_CF, quarticCmp_DF_of_zero hD0 hF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
        · -- F ties A
          have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
          refine QuarticSupportCone810.coneAF ?_
          refine ⟨hA, hF, hEqRaw_FA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_raw hRaw_CA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_GA_of_zero hG0 hA⟩
        · -- A strictly outranks F
          have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
          have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
          refine QuarticSupportCone810.coneA ?_
          refine ⟨hA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_raw hRaw_CA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, hRaw_FA, quarticCmp_GA_of_zero hG0 hA⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_ACG
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB0 : B.natDegree = 0)
    (hC : 0 < C.natDegree)
    (hD0 : D.natDegree = 0)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG : 0 < G.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hAClt : 2 * A.natDegree < C.natDegree
  · -- C strictly outranks A
    have hRaw_AC : 4 * A.natDegree < 2 * C.natDegree := quarticCmp_AC_to_raw hAClt
    by_cases hCGlt : 2 * C.natDegree < G.natDegree
    · -- G strictly outranks C
      have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticCmp_CG_to_raw hCGlt
      have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_ACG hRaw_AC hRaw_CG
      refine QuarticSupportCone810.coneG ?_
      refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_raw hRaw_CG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
    · by_cases hCGeq : 2 * C.natDegree = G.natDegree
      · -- G ties C
        have hEqRaw_GC : 4 * G.natDegree = 8 * C.natDegree := quarticEq_GC_to_raw (hCGeq.symm)
        refine QuarticSupportCone810.coneCG ?_
        refine ⟨hC, hG, quarticEq_GC_of_raw hEqRaw_GC, quarticCmp_AC_of_raw hRaw_AC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_FC_of_zero hF0 hC⟩
      · -- C strictly outranks G
        have hRed_GC : G.natDegree < 2 * C.natDegree := quarticScore_not_lt_not_eq hCGlt hCGeq
        have hRaw_GC : 4 * G.natDegree < 8 * C.natDegree := quarticCmp_GC_to_raw hRed_GC
        refine QuarticSupportCone810.coneC ?_
        refine ⟨hC, quarticCmp_AC_of_raw hRaw_AC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_raw hRaw_GC⟩
  · by_cases hACeq : 2 * A.natDegree = C.natDegree
    · -- C ties A
      have hEqRaw_CA : 2 * C.natDegree = 4 * A.natDegree := quarticEq_CA_to_raw (hACeq.symm)
      by_cases hAGlt : 4 * A.natDegree < G.natDegree
      · -- G strictly outranks AC
        have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
        have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_eq_lt_CAG hEqRaw_CA hRaw_AG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_raw hRaw_CG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
      · by_cases hAGeq : 4 * A.natDegree = G.natDegree
        · -- G ties AC
          have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
          refine QuarticSupportCone810.coneACG ?_
          refine ⟨hA, hC, hG, quarticEq_CA_of_raw hEqRaw_CA, quarticEq_GA_of_raw hEqRaw_GA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA⟩
        · -- AC strictly outranks G
          have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
          have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
          refine QuarticSupportCone810.coneAC ?_
          refine ⟨hA, hC, quarticEq_CA_of_raw hEqRaw_CA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_raw hRaw_GA⟩
    · -- A strictly outranks C
      have hRed_CA : C.natDegree < 2 * A.natDegree := quarticScore_not_lt_not_eq hAClt hACeq
      have hRaw_CA : 2 * C.natDegree < 4 * A.natDegree := quarticCmp_CA_to_raw hRed_CA
      by_cases hAGlt : 4 * A.natDegree < G.natDegree
      · -- G strictly outranks A
        have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
        have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CAG hRaw_CA hRaw_AG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_raw hRaw_CG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
      · by_cases hAGeq : 4 * A.natDegree = G.natDegree
        · -- G ties A
          have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
          refine QuarticSupportCone810.coneAG ?_
          refine ⟨hA, hG, quarticEq_GA_of_raw hEqRaw_GA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_raw hRaw_CA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA⟩
        · -- A strictly outranks G
          have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
          have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
          refine QuarticSupportCone810.coneA ?_
          refine ⟨hA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_raw hRaw_CA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_raw hRaw_GA⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_ADE
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB0 : B.natDegree = 0)
    (hC0 : C.natDegree = 0)
    (hD : 0 < D.natDegree)
    (hE : 0 < E.natDegree)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
  · -- D strictly outranks A
    have hRaw_AD : 5 * A.natDegree < 2 * D.natDegree := hADlt
    by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
    · -- E strictly outranks D
      have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := hDElt
      have hRaw_AE : 6 * A.natDegree < 2 * E.natDegree := quarticScore_lt_trans_ADE hRaw_AD hRaw_DE
      refine QuarticSupportCone810.coneE ?_
      refine ⟨hE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_zero hC0 hE, hRaw_DE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
    · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
      · -- E ties D
        have hEqRaw_ED : 5 * E.natDegree = 6 * D.natDegree := hDEeq.symm
        refine QuarticSupportCone810.coneDE ?_
        refine ⟨hD, hE, hEqRaw_ED, hRaw_AD, quarticCmp_BD_of_zero hB0 hD, quarticCmp_CD_of_zero hC0 hD, quarticCmp_FD_of_zero hF0 hD, quarticCmp_GD_of_zero hG0 hD⟩
      · -- D strictly outranks E
        have hRed_ED : 5 * E.natDegree < 6 * D.natDegree := quarticScore_not_lt_not_eq hDElt hDEeq
        have hRaw_ED : 5 * E.natDegree < 6 * D.natDegree := hRed_ED
        refine QuarticSupportCone810.coneD ?_
        refine ⟨hD, hRaw_AD, quarticCmp_BD_of_zero hB0 hD, quarticCmp_CD_of_zero hC0 hD, hRaw_ED, quarticCmp_FD_of_zero hF0 hD, quarticCmp_GD_of_zero hG0 hD⟩
  · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
    · -- D ties A
      have hEqRaw_DA : 2 * D.natDegree = 5 * A.natDegree := hADeq.symm
      by_cases hAElt : 3 * A.natDegree < E.natDegree
      · -- E strictly outranks AD
        have hRaw_AE : 6 * A.natDegree < 2 * E.natDegree := quarticCmp_AE_to_raw hAElt
        have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := quarticScore_eq_lt_DAE hEqRaw_DA hRaw_AE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_zero hC0 hE, hRaw_DE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
      · by_cases hAEeq : 3 * A.natDegree = E.natDegree
        · -- E ties AD
          have hEqRaw_EA : 2 * E.natDegree = 6 * A.natDegree := quarticEq_EA_to_raw (hAEeq.symm)
          refine QuarticSupportCone810.coneADE ?_
          refine ⟨hA, hD, hE, hEqRaw_DA, quarticEq_EA_of_raw hEqRaw_EA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩
        · -- AD strictly outranks E
          have hRed_EA : E.natDegree < 3 * A.natDegree := quarticScore_not_lt_not_eq hAElt hAEeq
          have hRaw_EA : 2 * E.natDegree < 6 * A.natDegree := quarticCmp_EA_to_raw hRed_EA
          refine QuarticSupportCone810.coneAD ?_
          refine ⟨hA, hD, hEqRaw_DA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_EA_of_raw hRaw_EA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩
    · -- A strictly outranks D
      have hRed_DA : 2 * D.natDegree < 5 * A.natDegree := quarticScore_not_lt_not_eq hADlt hADeq
      have hRaw_DA : 2 * D.natDegree < 5 * A.natDegree := hRed_DA
      by_cases hAElt : 3 * A.natDegree < E.natDegree
      · -- E strictly outranks A
        have hRaw_AE : 6 * A.natDegree < 2 * E.natDegree := quarticCmp_AE_to_raw hAElt
        have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := quarticScore_lt_trans_DAE hRaw_DA hRaw_AE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_zero hC0 hE, hRaw_DE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
      · by_cases hAEeq : 3 * A.natDegree = E.natDegree
        · -- E ties A
          have hEqRaw_EA : 2 * E.natDegree = 6 * A.natDegree := quarticEq_EA_to_raw (hAEeq.symm)
          refine QuarticSupportCone810.coneAE ?_
          refine ⟨hA, hE, quarticEq_EA_of_raw hEqRaw_EA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, hRaw_DA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩
        · -- A strictly outranks E
          have hRed_EA : E.natDegree < 3 * A.natDegree := quarticScore_not_lt_not_eq hAElt hAEeq
          have hRaw_EA : 2 * E.natDegree < 6 * A.natDegree := quarticCmp_EA_to_raw hRed_EA
          refine QuarticSupportCone810.coneA ?_
          refine ⟨hA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, hRaw_DA, quarticCmp_EA_of_raw hRaw_EA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_zero hG0 hA⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_ADF
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB0 : B.natDegree = 0)
    (hC0 : C.natDegree = 0)
    (hD : 0 < D.natDegree)
    (hE0 : E.natDegree = 0)
    (hF : 0 < F.natDegree)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
  · -- D strictly outranks A
    have hRaw_AD : 5 * A.natDegree < 2 * D.natDegree := hADlt
    by_cases hDFlt : 7 * D.natDegree < 5 * F.natDegree
    · -- F strictly outranks D
      have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := hDFlt
      have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := quarticScore_lt_trans_ADF hRaw_AD hRaw_DF
      refine QuarticSupportCone810.coneF ?_
      refine ⟨hF, hRaw_AF, quarticCmp_BF_of_zero hB0 hF, quarticCmp_CF_of_zero hC0 hF, hRaw_DF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
    · by_cases hDFeq : 7 * D.natDegree = 5 * F.natDegree
      · -- F ties D
        have hEqRaw_FD : 5 * F.natDegree = 7 * D.natDegree := hDFeq.symm
        refine QuarticSupportCone810.coneDF ?_
        refine ⟨hD, hF, hEqRaw_FD, hRaw_AD, quarticCmp_BD_of_zero hB0 hD, quarticCmp_CD_of_zero hC0 hD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_GD_of_zero hG0 hD⟩
      · -- D strictly outranks F
        have hRed_FD : 5 * F.natDegree < 7 * D.natDegree := quarticScore_not_lt_not_eq hDFlt hDFeq
        have hRaw_FD : 5 * F.natDegree < 7 * D.natDegree := hRed_FD
        refine QuarticSupportCone810.coneD ?_
        refine ⟨hD, hRaw_AD, quarticCmp_BD_of_zero hB0 hD, quarticCmp_CD_of_zero hC0 hD, quarticCmp_ED_of_zero hE0 hD, hRaw_FD, quarticCmp_GD_of_zero hG0 hD⟩
  · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
    · -- D ties A
      have hEqRaw_DA : 2 * D.natDegree = 5 * A.natDegree := hADeq.symm
      by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
      · -- F strictly outranks AD
        have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
        have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_eq_lt_DAF hEqRaw_DA hRaw_AF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, hRaw_AF, quarticCmp_BF_of_zero hB0 hF, quarticCmp_CF_of_zero hC0 hF, hRaw_DF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
        · -- F ties AD
          have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
          refine QuarticSupportCone810.coneADF ?_
          refine ⟨hA, hD, hF, hEqRaw_DA, hEqRaw_FA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_GA_of_zero hG0 hA⟩
        · -- AD strictly outranks F
          have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
          have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
          refine QuarticSupportCone810.coneAD ?_
          refine ⟨hA, hD, hEqRaw_DA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_EA_of_zero hE0 hA, hRaw_FA, quarticCmp_GA_of_zero hG0 hA⟩
    · -- A strictly outranks D
      have hRed_DA : 2 * D.natDegree < 5 * A.natDegree := quarticScore_not_lt_not_eq hADlt hADeq
      have hRaw_DA : 2 * D.natDegree < 5 * A.natDegree := hRed_DA
      by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
      · -- F strictly outranks A
        have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
        have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_lt_trans_DAF hRaw_DA hRaw_AF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, hRaw_AF, quarticCmp_BF_of_zero hB0 hF, quarticCmp_CF_of_zero hC0 hF, hRaw_DF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
        · -- F ties A
          have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
          refine QuarticSupportCone810.coneAF ?_
          refine ⟨hA, hF, hEqRaw_FA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, hRaw_DA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_GA_of_zero hG0 hA⟩
        · -- A strictly outranks F
          have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
          have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
          refine QuarticSupportCone810.coneA ?_
          refine ⟨hA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, hRaw_DA, quarticCmp_EA_of_zero hE0 hA, hRaw_FA, quarticCmp_GA_of_zero hG0 hA⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_ADG
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB0 : B.natDegree = 0)
    (hC0 : C.natDegree = 0)
    (hD : 0 < D.natDegree)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG : 0 < G.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
  · -- D strictly outranks A
    have hRaw_AD : 5 * A.natDegree < 2 * D.natDegree := hADlt
    by_cases hDGlt : 8 * D.natDegree < 5 * G.natDegree
    · -- G strictly outranks D
      have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := hDGlt
      have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_ADG hRaw_AD hRaw_DG
      refine QuarticSupportCone810.coneG ?_
      refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_zero hC0 hG, hRaw_DG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
    · by_cases hDGeq : 8 * D.natDegree = 5 * G.natDegree
      · -- G ties D
        have hEqRaw_GD : 5 * G.natDegree = 8 * D.natDegree := hDGeq.symm
        refine QuarticSupportCone810.coneDG ?_
        refine ⟨hD, hG, hEqRaw_GD, hRaw_AD, quarticCmp_BD_of_zero hB0 hD, quarticCmp_CD_of_zero hC0 hD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_FD_of_zero hF0 hD⟩
      · -- D strictly outranks G
        have hRed_GD : 5 * G.natDegree < 8 * D.natDegree := quarticScore_not_lt_not_eq hDGlt hDGeq
        have hRaw_GD : 5 * G.natDegree < 8 * D.natDegree := hRed_GD
        refine QuarticSupportCone810.coneD ?_
        refine ⟨hD, hRaw_AD, quarticCmp_BD_of_zero hB0 hD, quarticCmp_CD_of_zero hC0 hD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_FD_of_zero hF0 hD, hRaw_GD⟩
  · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
    · -- D ties A
      have hEqRaw_DA : 2 * D.natDegree = 5 * A.natDegree := hADeq.symm
      by_cases hAGlt : 4 * A.natDegree < G.natDegree
      · -- G strictly outranks AD
        have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
        have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_eq_lt_DAG hEqRaw_DA hRaw_AG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_zero hC0 hG, hRaw_DG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
      · by_cases hAGeq : 4 * A.natDegree = G.natDegree
        · -- G ties AD
          have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
          refine QuarticSupportCone810.coneADG ?_
          refine ⟨hA, hD, hG, hEqRaw_DA, quarticEq_GA_of_raw hEqRaw_GA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA⟩
        · -- AD strictly outranks G
          have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
          have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
          refine QuarticSupportCone810.coneAD ?_
          refine ⟨hA, hD, hEqRaw_DA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_raw hRaw_GA⟩
    · -- A strictly outranks D
      have hRed_DA : 2 * D.natDegree < 5 * A.natDegree := quarticScore_not_lt_not_eq hADlt hADeq
      have hRaw_DA : 2 * D.natDegree < 5 * A.natDegree := hRed_DA
      by_cases hAGlt : 4 * A.natDegree < G.natDegree
      · -- G strictly outranks A
        have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
        have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DAG hRaw_DA hRaw_AG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_zero hC0 hG, hRaw_DG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
      · by_cases hAGeq : 4 * A.natDegree = G.natDegree
        · -- G ties A
          have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
          refine QuarticSupportCone810.coneAG ?_
          refine ⟨hA, hG, quarticEq_GA_of_raw hEqRaw_GA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, hRaw_DA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA⟩
        · -- A strictly outranks G
          have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
          have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
          refine QuarticSupportCone810.coneA ?_
          refine ⟨hA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, hRaw_DA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_raw hRaw_GA⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_AEF
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB0 : B.natDegree = 0)
    (hC0 : C.natDegree = 0)
    (hD0 : D.natDegree = 0)
    (hE : 0 < E.natDegree)
    (hF : 0 < F.natDegree)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hAElt : 3 * A.natDegree < E.natDegree
  · -- E strictly outranks A
    have hRaw_AE : 6 * A.natDegree < 2 * E.natDegree := quarticCmp_AE_to_raw hAElt
    by_cases hEFlt : 7 * E.natDegree < 6 * F.natDegree
    · -- F strictly outranks E
      have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := hEFlt
      have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := quarticScore_lt_trans_AEF hRaw_AE hRaw_EF
      refine QuarticSupportCone810.coneF ?_
      refine ⟨hF, hRaw_AF, quarticCmp_BF_of_zero hB0 hF, quarticCmp_CF_of_zero hC0 hF, quarticCmp_DF_of_zero hD0 hF, hRaw_EF, quarticCmp_GF_of_zero hG0 hF⟩
    · by_cases hEFeq : 7 * E.natDegree = 6 * F.natDegree
      · -- F ties E
        have hEqRaw_FE : 6 * F.natDegree = 7 * E.natDegree := hEFeq.symm
        refine QuarticSupportCone810.coneEF ?_
        refine ⟨hE, hF, hEqRaw_FE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_zero hC0 hE, quarticCmp_DE_of_zero hD0 hE, quarticCmp_GE_of_zero hG0 hE⟩
      · -- E strictly outranks F
        have hRed_FE : 6 * F.natDegree < 7 * E.natDegree := quarticScore_not_lt_not_eq hEFlt hEFeq
        have hRaw_FE : 6 * F.natDegree < 7 * E.natDegree := hRed_FE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_zero hC0 hE, quarticCmp_DE_of_zero hD0 hE, hRaw_FE, quarticCmp_GE_of_zero hG0 hE⟩
  · by_cases hAEeq : 3 * A.natDegree = E.natDegree
    · -- E ties A
      have hEqRaw_EA : 2 * E.natDegree = 6 * A.natDegree := quarticEq_EA_to_raw (hAEeq.symm)
      by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
      · -- F strictly outranks AE
        have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
        have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_eq_lt_EAF hEqRaw_EA hRaw_AF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, hRaw_AF, quarticCmp_BF_of_zero hB0 hF, quarticCmp_CF_of_zero hC0 hF, quarticCmp_DF_of_zero hD0 hF, hRaw_EF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
        · -- F ties AE
          have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
          refine QuarticSupportCone810.coneAEF ?_
          refine ⟨hA, hE, hF, quarticEq_EA_of_raw hEqRaw_EA, hEqRaw_FA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_GA_of_zero hG0 hA⟩
        · -- AE strictly outranks F
          have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
          have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
          refine QuarticSupportCone810.coneAE ?_
          refine ⟨hA, hE, quarticEq_EA_of_raw hEqRaw_EA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, hRaw_FA, quarticCmp_GA_of_zero hG0 hA⟩
    · -- A strictly outranks E
      have hRed_EA : E.natDegree < 3 * A.natDegree := quarticScore_not_lt_not_eq hAElt hAEeq
      have hRaw_EA : 2 * E.natDegree < 6 * A.natDegree := quarticCmp_EA_to_raw hRed_EA
      by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
      · -- F strictly outranks A
        have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
        have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_lt_trans_EAF hRaw_EA hRaw_AF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, hRaw_AF, quarticCmp_BF_of_zero hB0 hF, quarticCmp_CF_of_zero hC0 hF, quarticCmp_DF_of_zero hD0 hF, hRaw_EF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
        · -- F ties A
          have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
          refine QuarticSupportCone810.coneAF ?_
          refine ⟨hA, hF, hEqRaw_FA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_raw hRaw_EA, quarticCmp_GA_of_zero hG0 hA⟩
        · -- A strictly outranks F
          have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
          have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
          refine QuarticSupportCone810.coneA ?_
          refine ⟨hA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_raw hRaw_EA, hRaw_FA, quarticCmp_GA_of_zero hG0 hA⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_AEG
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB0 : B.natDegree = 0)
    (hC0 : C.natDegree = 0)
    (hD0 : D.natDegree = 0)
    (hE : 0 < E.natDegree)
    (hF0 : F.natDegree = 0)
    (hG : 0 < G.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hAElt : 3 * A.natDegree < E.natDegree
  · -- E strictly outranks A
    have hRaw_AE : 6 * A.natDegree < 2 * E.natDegree := quarticCmp_AE_to_raw hAElt
    by_cases hEGlt : 4 * E.natDegree < 3 * G.natDegree
    · -- G strictly outranks E
      have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticCmp_EG_to_raw hEGlt
      have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AEG hRaw_AE hRaw_EG
      refine QuarticSupportCone810.coneG ?_
      refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_zero hC0 hG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_raw hRaw_EG, quarticCmp_FG_of_zero hF0 hG⟩
    · by_cases hEGeq : 4 * E.natDegree = 3 * G.natDegree
      · -- G ties E
        have hEqRaw_GE : 6 * G.natDegree = 8 * E.natDegree := quarticEq_GE_to_raw (hEGeq.symm)
        refine QuarticSupportCone810.coneEG ?_
        refine ⟨hE, hG, quarticEq_GE_of_raw hEqRaw_GE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_zero hC0 hE, quarticCmp_DE_of_zero hD0 hE, quarticCmp_FE_of_zero hF0 hE⟩
      · -- E strictly outranks G
        have hRed_GE : 3 * G.natDegree < 4 * E.natDegree := quarticScore_not_lt_not_eq hEGlt hEGeq
        have hRaw_GE : 6 * G.natDegree < 8 * E.natDegree := quarticCmp_GE_to_raw hRed_GE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_zero hC0 hE, quarticCmp_DE_of_zero hD0 hE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_raw hRaw_GE⟩
  · by_cases hAEeq : 3 * A.natDegree = E.natDegree
    · -- E ties A
      have hEqRaw_EA : 2 * E.natDegree = 6 * A.natDegree := quarticEq_EA_to_raw (hAEeq.symm)
      by_cases hAGlt : 4 * A.natDegree < G.natDegree
      · -- G strictly outranks AE
        have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
        have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_eq_lt_EAG hEqRaw_EA hRaw_AG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_zero hC0 hG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_raw hRaw_EG, quarticCmp_FG_of_zero hF0 hG⟩
      · by_cases hAGeq : 4 * A.natDegree = G.natDegree
        · -- G ties AE
          have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
          refine QuarticSupportCone810.coneAEG ?_
          refine ⟨hA, hE, hG, quarticEq_EA_of_raw hEqRaw_EA, quarticEq_GA_of_raw hEqRaw_GA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_FA_of_zero hF0 hA⟩
        · -- AE strictly outranks G
          have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
          have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
          refine QuarticSupportCone810.coneAE ?_
          refine ⟨hA, hE, quarticEq_EA_of_raw hEqRaw_EA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_raw hRaw_GA⟩
    · -- A strictly outranks E
      have hRed_EA : E.natDegree < 3 * A.natDegree := quarticScore_not_lt_not_eq hAElt hAEeq
      have hRaw_EA : 2 * E.natDegree < 6 * A.natDegree := quarticCmp_EA_to_raw hRed_EA
      by_cases hAGlt : 4 * A.natDegree < G.natDegree
      · -- G strictly outranks A
        have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
        have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EAG hRaw_EA hRaw_AG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_zero hC0 hG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_raw hRaw_EG, quarticCmp_FG_of_zero hF0 hG⟩
      · by_cases hAGeq : 4 * A.natDegree = G.natDegree
        · -- G ties A
          have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
          refine QuarticSupportCone810.coneAG ?_
          refine ⟨hA, hG, quarticEq_GA_of_raw hEqRaw_GA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_raw hRaw_EA, quarticCmp_FA_of_zero hF0 hA⟩
        · -- A strictly outranks G
          have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
          have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
          refine QuarticSupportCone810.coneA ?_
          refine ⟨hA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_raw hRaw_EA, quarticCmp_FA_of_zero hF0 hA, quarticCmp_GA_of_raw hRaw_GA⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_AFG
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB0 : B.natDegree = 0)
    (hC0 : C.natDegree = 0)
    (hD0 : D.natDegree = 0)
    (hE0 : E.natDegree = 0)
    (hF : 0 < F.natDegree)
    (hG : 0 < G.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
  · -- F strictly outranks A
    have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
    by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
    · -- G strictly outranks F
      have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
      have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
      refine QuarticSupportCone810.coneG ?_
      refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_zero hC0 hG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_zero hE0 hG, hRaw_FG⟩
    · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
      · -- G ties F
        have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
        refine QuarticSupportCone810.coneFG ?_
        refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, quarticCmp_BF_of_zero hB0 hF, quarticCmp_CF_of_zero hC0 hF, quarticCmp_DF_of_zero hD0 hF, quarticCmp_EF_of_zero hE0 hF⟩
      · -- F strictly outranks G
        have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
        have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, hRaw_AF, quarticCmp_BF_of_zero hB0 hF, quarticCmp_CF_of_zero hC0 hF, quarticCmp_DF_of_zero hD0 hF, quarticCmp_EF_of_zero hE0 hF, hRaw_GF⟩
  · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
    · -- F ties A
      have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
      by_cases hAGlt : 4 * A.natDegree < G.natDegree
      · -- G strictly outranks AF
        have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
        have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FAG hEqRaw_FA hRaw_AG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_zero hC0 hG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_zero hE0 hG, hRaw_FG⟩
      · by_cases hAGeq : 4 * A.natDegree = G.natDegree
        · -- G ties AF
          have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
          refine QuarticSupportCone810.coneAFG ?_
          refine ⟨hA, hF, hG, hEqRaw_FA, quarticEq_GA_of_raw hEqRaw_GA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA⟩
        · -- AF strictly outranks G
          have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
          have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
          refine QuarticSupportCone810.coneAF ?_
          refine ⟨hA, hF, hEqRaw_FA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, quarticCmp_GA_of_raw hRaw_GA⟩
    · -- A strictly outranks F
      have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
      have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
      by_cases hAGlt : 4 * A.natDegree < G.natDegree
      · -- G strictly outranks A
        have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
        have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FAG hRaw_FA hRaw_AG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_zero hC0 hG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_zero hE0 hG, hRaw_FG⟩
      · by_cases hAGeq : 4 * A.natDegree = G.natDegree
        · -- G ties A
          have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
          refine QuarticSupportCone810.coneAG ?_
          refine ⟨hA, hG, quarticEq_GA_of_raw hEqRaw_GA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, hRaw_FA⟩
        · -- A strictly outranks G
          have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
          have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
          refine QuarticSupportCone810.coneA ?_
          refine ⟨hA, quarticCmp_BA_of_zero hB0 hA, quarticCmp_CA_of_zero hC0 hA, quarticCmp_DA_of_zero hD0 hA, quarticCmp_EA_of_zero hE0 hA, hRaw_FA, quarticCmp_GA_of_raw hRaw_GA⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_BCD
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB : 0 < B.natDegree)
    (hC : 0 < C.natDegree)
    (hD : 0 < D.natDegree)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hBClt : 4 * B.natDegree < 3 * C.natDegree
  · -- C strictly outranks B
    have hRaw_BC : 4 * B.natDegree < 3 * C.natDegree := hBClt
    by_cases hCDlt : 5 * C.natDegree < 4 * D.natDegree
    · -- D strictly outranks C
      have hRaw_CD : 5 * C.natDegree < 4 * D.natDegree := hCDlt
      have hRaw_BD : 5 * B.natDegree < 3 * D.natDegree := quarticScore_lt_trans_BCD hRaw_BC hRaw_CD
      refine QuarticSupportCone810.coneD ?_
      refine ⟨hD, quarticCmp_AD_of_zero hA0 hD, hRaw_BD, hRaw_CD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_FD_of_zero hF0 hD, quarticCmp_GD_of_zero hG0 hD⟩
    · by_cases hCDeq : 5 * C.natDegree = 4 * D.natDegree
      · -- D ties C
        have hEqRaw_DC : 4 * D.natDegree = 5 * C.natDegree := hCDeq.symm
        refine QuarticSupportCone810.coneCD ?_
        refine ⟨hC, hD, hEqRaw_DC, quarticCmp_AC_of_zero hA0 hC, hRaw_BC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_zero hG0 hC⟩
      · -- C strictly outranks D
        have hRed_DC : 4 * D.natDegree < 5 * C.natDegree := quarticScore_not_lt_not_eq hCDlt hCDeq
        have hRaw_DC : 4 * D.natDegree < 5 * C.natDegree := hRed_DC
        refine QuarticSupportCone810.coneC ?_
        refine ⟨hC, quarticCmp_AC_of_zero hA0 hC, hRaw_BC, hRaw_DC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_zero hG0 hC⟩
  · by_cases hBCeq : 4 * B.natDegree = 3 * C.natDegree
    · -- C ties B
      have hEqRaw_CB : 3 * C.natDegree = 4 * B.natDegree := hBCeq.symm
      by_cases hBDlt : 5 * B.natDegree < 3 * D.natDegree
      · -- D strictly outranks BC
        have hRaw_BD : 5 * B.natDegree < 3 * D.natDegree := hBDlt
        have hRaw_CD : 5 * C.natDegree < 4 * D.natDegree := quarticScore_eq_lt_CBD hEqRaw_CB hRaw_BD
        refine QuarticSupportCone810.coneD ?_
        refine ⟨hD, quarticCmp_AD_of_zero hA0 hD, hRaw_BD, hRaw_CD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_FD_of_zero hF0 hD, quarticCmp_GD_of_zero hG0 hD⟩
      · by_cases hBDeq : 5 * B.natDegree = 3 * D.natDegree
        · -- D ties BC
          have hEqRaw_DB : 3 * D.natDegree = 5 * B.natDegree := hBDeq.symm
          refine QuarticSupportCone810.coneBCD ?_
          refine ⟨hB, hC, hD, hEqRaw_CB, hEqRaw_DB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_FB_of_zero hF0 hB, quarticCmp_GB_of_zero hG0 hB⟩
        · -- BC strictly outranks D
          have hRed_DB : 3 * D.natDegree < 5 * B.natDegree := quarticScore_not_lt_not_eq hBDlt hBDeq
          have hRaw_DB : 3 * D.natDegree < 5 * B.natDegree := hRed_DB
          refine QuarticSupportCone810.coneBC ?_
          refine ⟨hB, hC, hEqRaw_CB, quarticCmp_AB_of_zero hA0 hB, hRaw_DB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_FB_of_zero hF0 hB, quarticCmp_GB_of_zero hG0 hB⟩
    · -- B strictly outranks C
      have hRed_CB : 3 * C.natDegree < 4 * B.natDegree := quarticScore_not_lt_not_eq hBClt hBCeq
      have hRaw_CB : 3 * C.natDegree < 4 * B.natDegree := hRed_CB
      by_cases hBDlt : 5 * B.natDegree < 3 * D.natDegree
      · -- D strictly outranks B
        have hRaw_BD : 5 * B.natDegree < 3 * D.natDegree := hBDlt
        have hRaw_CD : 5 * C.natDegree < 4 * D.natDegree := quarticScore_lt_trans_CBD hRaw_CB hRaw_BD
        refine QuarticSupportCone810.coneD ?_
        refine ⟨hD, quarticCmp_AD_of_zero hA0 hD, hRaw_BD, hRaw_CD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_FD_of_zero hF0 hD, quarticCmp_GD_of_zero hG0 hD⟩
      · by_cases hBDeq : 5 * B.natDegree = 3 * D.natDegree
        · -- D ties B
          have hEqRaw_DB : 3 * D.natDegree = 5 * B.natDegree := hBDeq.symm
          refine QuarticSupportCone810.coneBD ?_
          refine ⟨hB, hD, hEqRaw_DB, quarticCmp_AB_of_zero hA0 hB, hRaw_CB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_FB_of_zero hF0 hB, quarticCmp_GB_of_zero hG0 hB⟩
        · -- B strictly outranks D
          have hRed_DB : 3 * D.natDegree < 5 * B.natDegree := quarticScore_not_lt_not_eq hBDlt hBDeq
          have hRaw_DB : 3 * D.natDegree < 5 * B.natDegree := hRed_DB
          refine QuarticSupportCone810.coneB ?_
          refine ⟨hB, quarticCmp_AB_of_zero hA0 hB, hRaw_CB, hRaw_DB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_FB_of_zero hF0 hB, quarticCmp_GB_of_zero hG0 hB⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_BCE
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB : 0 < B.natDegree)
    (hC : 0 < C.natDegree)
    (hD0 : D.natDegree = 0)
    (hE : 0 < E.natDegree)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hBClt : 4 * B.natDegree < 3 * C.natDegree
  · -- C strictly outranks B
    have hRaw_BC : 4 * B.natDegree < 3 * C.natDegree := hBClt
    by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
    · -- E strictly outranks C
      have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticCmp_CE_to_raw hCElt
      have hRaw_BE : 6 * B.natDegree < 3 * E.natDegree := quarticScore_lt_trans_BCE hRaw_BC hRaw_CE
      refine QuarticSupportCone810.coneE ?_
      refine ⟨hE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, quarticCmp_DE_of_zero hD0 hE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
    · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
      · -- E ties C
        have hEqRaw_EC : 4 * E.natDegree = 6 * C.natDegree := quarticEq_EC_to_raw (hCEeq.symm)
        refine QuarticSupportCone810.coneCE ?_
        refine ⟨hC, hE, quarticEq_EC_of_raw hEqRaw_EC, quarticCmp_AC_of_zero hA0 hC, hRaw_BC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_zero hG0 hC⟩
      · -- C strictly outranks E
        have hRed_EC : 2 * E.natDegree < 3 * C.natDegree := quarticScore_not_lt_not_eq hCElt hCEeq
        have hRaw_EC : 4 * E.natDegree < 6 * C.natDegree := quarticCmp_EC_to_raw hRed_EC
        refine QuarticSupportCone810.coneC ?_
        refine ⟨hC, quarticCmp_AC_of_zero hA0 hC, hRaw_BC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_EC_of_raw hRaw_EC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_zero hG0 hC⟩
  · by_cases hBCeq : 4 * B.natDegree = 3 * C.natDegree
    · -- C ties B
      have hEqRaw_CB : 3 * C.natDegree = 4 * B.natDegree := hBCeq.symm
      by_cases hBElt : 2 * B.natDegree < E.natDegree
      · -- E strictly outranks BC
        have hRaw_BE : 6 * B.natDegree < 3 * E.natDegree := quarticCmp_BE_to_raw hBElt
        have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticScore_eq_lt_CBE hEqRaw_CB hRaw_BE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, quarticCmp_DE_of_zero hD0 hE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
      · by_cases hBEeq : 2 * B.natDegree = E.natDegree
        · -- E ties BC
          have hEqRaw_EB : 3 * E.natDegree = 6 * B.natDegree := quarticEq_EB_to_raw (hBEeq.symm)
          refine QuarticSupportCone810.coneBCE ?_
          refine ⟨hB, hC, hE, hEqRaw_CB, quarticEq_EB_of_raw hEqRaw_EB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_FB_of_zero hF0 hB, quarticCmp_GB_of_zero hG0 hB⟩
        · -- BC strictly outranks E
          have hRed_EB : E.natDegree < 2 * B.natDegree := quarticScore_not_lt_not_eq hBElt hBEeq
          have hRaw_EB : 3 * E.natDegree < 6 * B.natDegree := quarticCmp_EB_to_raw hRed_EB
          refine QuarticSupportCone810.coneBC ?_
          refine ⟨hB, hC, hEqRaw_CB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_raw hRaw_EB, quarticCmp_FB_of_zero hF0 hB, quarticCmp_GB_of_zero hG0 hB⟩
    · -- B strictly outranks C
      have hRed_CB : 3 * C.natDegree < 4 * B.natDegree := quarticScore_not_lt_not_eq hBClt hBCeq
      have hRaw_CB : 3 * C.natDegree < 4 * B.natDegree := hRed_CB
      by_cases hBElt : 2 * B.natDegree < E.natDegree
      · -- E strictly outranks B
        have hRaw_BE : 6 * B.natDegree < 3 * E.natDegree := quarticCmp_BE_to_raw hBElt
        have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticScore_lt_trans_CBE hRaw_CB hRaw_BE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, quarticCmp_DE_of_zero hD0 hE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
      · by_cases hBEeq : 2 * B.natDegree = E.natDegree
        · -- E ties B
          have hEqRaw_EB : 3 * E.natDegree = 6 * B.natDegree := quarticEq_EB_to_raw (hBEeq.symm)
          refine QuarticSupportCone810.coneBE ?_
          refine ⟨hB, hE, quarticEq_EB_of_raw hEqRaw_EB, quarticCmp_AB_of_zero hA0 hB, hRaw_CB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_FB_of_zero hF0 hB, quarticCmp_GB_of_zero hG0 hB⟩
        · -- B strictly outranks E
          have hRed_EB : E.natDegree < 2 * B.natDegree := quarticScore_not_lt_not_eq hBElt hBEeq
          have hRaw_EB : 3 * E.natDegree < 6 * B.natDegree := quarticCmp_EB_to_raw hRed_EB
          refine QuarticSupportCone810.coneB ?_
          refine ⟨hB, quarticCmp_AB_of_zero hA0 hB, hRaw_CB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_raw hRaw_EB, quarticCmp_FB_of_zero hF0 hB, quarticCmp_GB_of_zero hG0 hB⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_BCF
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB : 0 < B.natDegree)
    (hC : 0 < C.natDegree)
    (hD0 : D.natDegree = 0)
    (hE0 : E.natDegree = 0)
    (hF : 0 < F.natDegree)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hBClt : 4 * B.natDegree < 3 * C.natDegree
  · -- C strictly outranks B
    have hRaw_BC : 4 * B.natDegree < 3 * C.natDegree := hBClt
    by_cases hCFlt : 7 * C.natDegree < 4 * F.natDegree
    · -- F strictly outranks C
      have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := hCFlt
      have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BCF hRaw_BC hRaw_CF
      refine QuarticSupportCone810.coneF ?_
      refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, hRaw_BF, hRaw_CF, quarticCmp_DF_of_zero hD0 hF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
    · by_cases hCFeq : 7 * C.natDegree = 4 * F.natDegree
      · -- F ties C
        have hEqRaw_FC : 4 * F.natDegree = 7 * C.natDegree := hCFeq.symm
        refine QuarticSupportCone810.coneCF ?_
        refine ⟨hC, hF, hEqRaw_FC, quarticCmp_AC_of_zero hA0 hC, hRaw_BC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_GC_of_zero hG0 hC⟩
      · -- C strictly outranks F
        have hRed_FC : 4 * F.natDegree < 7 * C.natDegree := quarticScore_not_lt_not_eq hCFlt hCFeq
        have hRaw_FC : 4 * F.natDegree < 7 * C.natDegree := hRed_FC
        refine QuarticSupportCone810.coneC ?_
        refine ⟨hC, quarticCmp_AC_of_zero hA0 hC, hRaw_BC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_EC_of_zero hE0 hC, hRaw_FC, quarticCmp_GC_of_zero hG0 hC⟩
  · by_cases hBCeq : 4 * B.natDegree = 3 * C.natDegree
    · -- C ties B
      have hEqRaw_CB : 3 * C.natDegree = 4 * B.natDegree := hBCeq.symm
      by_cases hBFlt : 7 * B.natDegree < 3 * F.natDegree
      · -- F strictly outranks BC
        have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := hBFlt
        have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_eq_lt_CBF hEqRaw_CB hRaw_BF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, hRaw_BF, hRaw_CF, quarticCmp_DF_of_zero hD0 hF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hBFeq : 7 * B.natDegree = 3 * F.natDegree
        · -- F ties BC
          have hEqRaw_FB : 3 * F.natDegree = 7 * B.natDegree := hBFeq.symm
          refine QuarticSupportCone810.coneBCF ?_
          refine ⟨hB, hC, hF, hEqRaw_CB, hEqRaw_FB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_GB_of_zero hG0 hB⟩
        · -- BC strictly outranks F
          have hRed_FB : 3 * F.natDegree < 7 * B.natDegree := quarticScore_not_lt_not_eq hBFlt hBFeq
          have hRaw_FB : 3 * F.natDegree < 7 * B.natDegree := hRed_FB
          refine QuarticSupportCone810.coneBC ?_
          refine ⟨hB, hC, hEqRaw_CB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_zero hE0 hB, hRaw_FB, quarticCmp_GB_of_zero hG0 hB⟩
    · -- B strictly outranks C
      have hRed_CB : 3 * C.natDegree < 4 * B.natDegree := quarticScore_not_lt_not_eq hBClt hBCeq
      have hRaw_CB : 3 * C.natDegree < 4 * B.natDegree := hRed_CB
      by_cases hBFlt : 7 * B.natDegree < 3 * F.natDegree
      · -- F strictly outranks B
        have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := hBFlt
        have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CBF hRaw_CB hRaw_BF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, hRaw_BF, hRaw_CF, quarticCmp_DF_of_zero hD0 hF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hBFeq : 7 * B.natDegree = 3 * F.natDegree
        · -- F ties B
          have hEqRaw_FB : 3 * F.natDegree = 7 * B.natDegree := hBFeq.symm
          refine QuarticSupportCone810.coneBF ?_
          refine ⟨hB, hF, hEqRaw_FB, quarticCmp_AB_of_zero hA0 hB, hRaw_CB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_GB_of_zero hG0 hB⟩
        · -- B strictly outranks F
          have hRed_FB : 3 * F.natDegree < 7 * B.natDegree := quarticScore_not_lt_not_eq hBFlt hBFeq
          have hRaw_FB : 3 * F.natDegree < 7 * B.natDegree := hRed_FB
          refine QuarticSupportCone810.coneB ?_
          refine ⟨hB, quarticCmp_AB_of_zero hA0 hB, hRaw_CB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_zero hE0 hB, hRaw_FB, quarticCmp_GB_of_zero hG0 hB⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_BCG
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB : 0 < B.natDegree)
    (hC : 0 < C.natDegree)
    (hD0 : D.natDegree = 0)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG : 0 < G.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hBClt : 4 * B.natDegree < 3 * C.natDegree
  · -- C strictly outranks B
    have hRaw_BC : 4 * B.natDegree < 3 * C.natDegree := hBClt
    by_cases hCGlt : 2 * C.natDegree < G.natDegree
    · -- G strictly outranks C
      have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticCmp_CG_to_raw hCGlt
      have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BCG hRaw_BC hRaw_CG
      refine QuarticSupportCone810.coneG ?_
      refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
    · by_cases hCGeq : 2 * C.natDegree = G.natDegree
      · -- G ties C
        have hEqRaw_GC : 4 * G.natDegree = 8 * C.natDegree := quarticEq_GC_to_raw (hCGeq.symm)
        refine QuarticSupportCone810.coneCG ?_
        refine ⟨hC, hG, quarticEq_GC_of_raw hEqRaw_GC, quarticCmp_AC_of_zero hA0 hC, hRaw_BC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_FC_of_zero hF0 hC⟩
      · -- C strictly outranks G
        have hRed_GC : G.natDegree < 2 * C.natDegree := quarticScore_not_lt_not_eq hCGlt hCGeq
        have hRaw_GC : 4 * G.natDegree < 8 * C.natDegree := quarticCmp_GC_to_raw hRed_GC
        refine QuarticSupportCone810.coneC ?_
        refine ⟨hC, quarticCmp_AC_of_zero hA0 hC, hRaw_BC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_raw hRaw_GC⟩
  · by_cases hBCeq : 4 * B.natDegree = 3 * C.natDegree
    · -- C ties B
      have hEqRaw_CB : 3 * C.natDegree = 4 * B.natDegree := hBCeq.symm
      by_cases hBGlt : 8 * B.natDegree < 3 * G.natDegree
      · -- G strictly outranks BC
        have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := hBGlt
        have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_eq_lt_CBG hEqRaw_CB hRaw_BG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
      · by_cases hBGeq : 8 * B.natDegree = 3 * G.natDegree
        · -- G ties BC
          have hEqRaw_GB : 3 * G.natDegree = 8 * B.natDegree := hBGeq.symm
          refine QuarticSupportCone810.coneBCG ?_
          refine ⟨hB, hC, hG, hEqRaw_CB, hEqRaw_GB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_FB_of_zero hF0 hB⟩
        · -- BC strictly outranks G
          have hRed_GB : 3 * G.natDegree < 8 * B.natDegree := quarticScore_not_lt_not_eq hBGlt hBGeq
          have hRaw_GB : 3 * G.natDegree < 8 * B.natDegree := hRed_GB
          refine QuarticSupportCone810.coneBC ?_
          refine ⟨hB, hC, hEqRaw_CB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_FB_of_zero hF0 hB, hRaw_GB⟩
    · -- B strictly outranks C
      have hRed_CB : 3 * C.natDegree < 4 * B.natDegree := quarticScore_not_lt_not_eq hBClt hBCeq
      have hRaw_CB : 3 * C.natDegree < 4 * B.natDegree := hRed_CB
      by_cases hBGlt : 8 * B.natDegree < 3 * G.natDegree
      · -- G strictly outranks B
        have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := hBGlt
        have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CBG hRaw_CB hRaw_BG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
      · by_cases hBGeq : 8 * B.natDegree = 3 * G.natDegree
        · -- G ties B
          have hEqRaw_GB : 3 * G.natDegree = 8 * B.natDegree := hBGeq.symm
          refine QuarticSupportCone810.coneBG ?_
          refine ⟨hB, hG, hEqRaw_GB, quarticCmp_AB_of_zero hA0 hB, hRaw_CB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_FB_of_zero hF0 hB⟩
        · -- B strictly outranks G
          have hRed_GB : 3 * G.natDegree < 8 * B.natDegree := quarticScore_not_lt_not_eq hBGlt hBGeq
          have hRaw_GB : 3 * G.natDegree < 8 * B.natDegree := hRed_GB
          refine QuarticSupportCone810.coneB ?_
          refine ⟨hB, quarticCmp_AB_of_zero hA0 hB, hRaw_CB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_FB_of_zero hF0 hB, hRaw_GB⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_BDE
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB : 0 < B.natDegree)
    (hC0 : C.natDegree = 0)
    (hD : 0 < D.natDegree)
    (hE : 0 < E.natDegree)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hBDlt : 5 * B.natDegree < 3 * D.natDegree
  · -- D strictly outranks B
    have hRaw_BD : 5 * B.natDegree < 3 * D.natDegree := hBDlt
    by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
    · -- E strictly outranks D
      have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := hDElt
      have hRaw_BE : 6 * B.natDegree < 3 * E.natDegree := quarticScore_lt_trans_BDE hRaw_BD hRaw_DE
      refine QuarticSupportCone810.coneE ?_
      refine ⟨hE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_zero hC0 hE, hRaw_DE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
    · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
      · -- E ties D
        have hEqRaw_ED : 5 * E.natDegree = 6 * D.natDegree := hDEeq.symm
        refine QuarticSupportCone810.coneDE ?_
        refine ⟨hD, hE, hEqRaw_ED, quarticCmp_AD_of_zero hA0 hD, hRaw_BD, quarticCmp_CD_of_zero hC0 hD, quarticCmp_FD_of_zero hF0 hD, quarticCmp_GD_of_zero hG0 hD⟩
      · -- D strictly outranks E
        have hRed_ED : 5 * E.natDegree < 6 * D.natDegree := quarticScore_not_lt_not_eq hDElt hDEeq
        have hRaw_ED : 5 * E.natDegree < 6 * D.natDegree := hRed_ED
        refine QuarticSupportCone810.coneD ?_
        refine ⟨hD, quarticCmp_AD_of_zero hA0 hD, hRaw_BD, quarticCmp_CD_of_zero hC0 hD, hRaw_ED, quarticCmp_FD_of_zero hF0 hD, quarticCmp_GD_of_zero hG0 hD⟩
  · by_cases hBDeq : 5 * B.natDegree = 3 * D.natDegree
    · -- D ties B
      have hEqRaw_DB : 3 * D.natDegree = 5 * B.natDegree := hBDeq.symm
      by_cases hBElt : 2 * B.natDegree < E.natDegree
      · -- E strictly outranks BD
        have hRaw_BE : 6 * B.natDegree < 3 * E.natDegree := quarticCmp_BE_to_raw hBElt
        have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := quarticScore_eq_lt_DBE hEqRaw_DB hRaw_BE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_zero hC0 hE, hRaw_DE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
      · by_cases hBEeq : 2 * B.natDegree = E.natDegree
        · -- E ties BD
          have hEqRaw_EB : 3 * E.natDegree = 6 * B.natDegree := quarticEq_EB_to_raw (hBEeq.symm)
          refine QuarticSupportCone810.coneBDE ?_
          refine ⟨hB, hD, hE, hEqRaw_DB, quarticEq_EB_of_raw hEqRaw_EB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_FB_of_zero hF0 hB, quarticCmp_GB_of_zero hG0 hB⟩
        · -- BD strictly outranks E
          have hRed_EB : E.natDegree < 2 * B.natDegree := quarticScore_not_lt_not_eq hBElt hBEeq
          have hRaw_EB : 3 * E.natDegree < 6 * B.natDegree := quarticCmp_EB_to_raw hRed_EB
          refine QuarticSupportCone810.coneBD ?_
          refine ⟨hB, hD, hEqRaw_DB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_EB_of_raw hRaw_EB, quarticCmp_FB_of_zero hF0 hB, quarticCmp_GB_of_zero hG0 hB⟩
    · -- B strictly outranks D
      have hRed_DB : 3 * D.natDegree < 5 * B.natDegree := quarticScore_not_lt_not_eq hBDlt hBDeq
      have hRaw_DB : 3 * D.natDegree < 5 * B.natDegree := hRed_DB
      by_cases hBElt : 2 * B.natDegree < E.natDegree
      · -- E strictly outranks B
        have hRaw_BE : 6 * B.natDegree < 3 * E.natDegree := quarticCmp_BE_to_raw hBElt
        have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := quarticScore_lt_trans_DBE hRaw_DB hRaw_BE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_zero hC0 hE, hRaw_DE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
      · by_cases hBEeq : 2 * B.natDegree = E.natDegree
        · -- E ties B
          have hEqRaw_EB : 3 * E.natDegree = 6 * B.natDegree := quarticEq_EB_to_raw (hBEeq.symm)
          refine QuarticSupportCone810.coneBE ?_
          refine ⟨hB, hE, quarticEq_EB_of_raw hEqRaw_EB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, hRaw_DB, quarticCmp_FB_of_zero hF0 hB, quarticCmp_GB_of_zero hG0 hB⟩
        · -- B strictly outranks E
          have hRed_EB : E.natDegree < 2 * B.natDegree := quarticScore_not_lt_not_eq hBElt hBEeq
          have hRaw_EB : 3 * E.natDegree < 6 * B.natDegree := quarticCmp_EB_to_raw hRed_EB
          refine QuarticSupportCone810.coneB ?_
          refine ⟨hB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, hRaw_DB, quarticCmp_EB_of_raw hRaw_EB, quarticCmp_FB_of_zero hF0 hB, quarticCmp_GB_of_zero hG0 hB⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_BDF
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB : 0 < B.natDegree)
    (hC0 : C.natDegree = 0)
    (hD : 0 < D.natDegree)
    (hE0 : E.natDegree = 0)
    (hF : 0 < F.natDegree)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hBDlt : 5 * B.natDegree < 3 * D.natDegree
  · -- D strictly outranks B
    have hRaw_BD : 5 * B.natDegree < 3 * D.natDegree := hBDlt
    by_cases hDFlt : 7 * D.natDegree < 5 * F.natDegree
    · -- F strictly outranks D
      have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := hDFlt
      have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BDF hRaw_BD hRaw_DF
      refine QuarticSupportCone810.coneF ?_
      refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, hRaw_BF, quarticCmp_CF_of_zero hC0 hF, hRaw_DF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
    · by_cases hDFeq : 7 * D.natDegree = 5 * F.natDegree
      · -- F ties D
        have hEqRaw_FD : 5 * F.natDegree = 7 * D.natDegree := hDFeq.symm
        refine QuarticSupportCone810.coneDF ?_
        refine ⟨hD, hF, hEqRaw_FD, quarticCmp_AD_of_zero hA0 hD, hRaw_BD, quarticCmp_CD_of_zero hC0 hD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_GD_of_zero hG0 hD⟩
      · -- D strictly outranks F
        have hRed_FD : 5 * F.natDegree < 7 * D.natDegree := quarticScore_not_lt_not_eq hDFlt hDFeq
        have hRaw_FD : 5 * F.natDegree < 7 * D.natDegree := hRed_FD
        refine QuarticSupportCone810.coneD ?_
        refine ⟨hD, quarticCmp_AD_of_zero hA0 hD, hRaw_BD, quarticCmp_CD_of_zero hC0 hD, quarticCmp_ED_of_zero hE0 hD, hRaw_FD, quarticCmp_GD_of_zero hG0 hD⟩
  · by_cases hBDeq : 5 * B.natDegree = 3 * D.natDegree
    · -- D ties B
      have hEqRaw_DB : 3 * D.natDegree = 5 * B.natDegree := hBDeq.symm
      by_cases hBFlt : 7 * B.natDegree < 3 * F.natDegree
      · -- F strictly outranks BD
        have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := hBFlt
        have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_eq_lt_DBF hEqRaw_DB hRaw_BF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, hRaw_BF, quarticCmp_CF_of_zero hC0 hF, hRaw_DF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hBFeq : 7 * B.natDegree = 3 * F.natDegree
        · -- F ties BD
          have hEqRaw_FB : 3 * F.natDegree = 7 * B.natDegree := hBFeq.symm
          refine QuarticSupportCone810.coneBDF ?_
          refine ⟨hB, hD, hF, hEqRaw_DB, hEqRaw_FB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_GB_of_zero hG0 hB⟩
        · -- BD strictly outranks F
          have hRed_FB : 3 * F.natDegree < 7 * B.natDegree := quarticScore_not_lt_not_eq hBFlt hBFeq
          have hRaw_FB : 3 * F.natDegree < 7 * B.natDegree := hRed_FB
          refine QuarticSupportCone810.coneBD ?_
          refine ⟨hB, hD, hEqRaw_DB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_EB_of_zero hE0 hB, hRaw_FB, quarticCmp_GB_of_zero hG0 hB⟩
    · -- B strictly outranks D
      have hRed_DB : 3 * D.natDegree < 5 * B.natDegree := quarticScore_not_lt_not_eq hBDlt hBDeq
      have hRaw_DB : 3 * D.natDegree < 5 * B.natDegree := hRed_DB
      by_cases hBFlt : 7 * B.natDegree < 3 * F.natDegree
      · -- F strictly outranks B
        have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := hBFlt
        have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_lt_trans_DBF hRaw_DB hRaw_BF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, hRaw_BF, quarticCmp_CF_of_zero hC0 hF, hRaw_DF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hBFeq : 7 * B.natDegree = 3 * F.natDegree
        · -- F ties B
          have hEqRaw_FB : 3 * F.natDegree = 7 * B.natDegree := hBFeq.symm
          refine QuarticSupportCone810.coneBF ?_
          refine ⟨hB, hF, hEqRaw_FB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, hRaw_DB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_GB_of_zero hG0 hB⟩
        · -- B strictly outranks F
          have hRed_FB : 3 * F.natDegree < 7 * B.natDegree := quarticScore_not_lt_not_eq hBFlt hBFeq
          have hRaw_FB : 3 * F.natDegree < 7 * B.natDegree := hRed_FB
          refine QuarticSupportCone810.coneB ?_
          refine ⟨hB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, hRaw_DB, quarticCmp_EB_of_zero hE0 hB, hRaw_FB, quarticCmp_GB_of_zero hG0 hB⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_BDG
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB : 0 < B.natDegree)
    (hC0 : C.natDegree = 0)
    (hD : 0 < D.natDegree)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG : 0 < G.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hBDlt : 5 * B.natDegree < 3 * D.natDegree
  · -- D strictly outranks B
    have hRaw_BD : 5 * B.natDegree < 3 * D.natDegree := hBDlt
    by_cases hDGlt : 8 * D.natDegree < 5 * G.natDegree
    · -- G strictly outranks D
      have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := hDGlt
      have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BDG hRaw_BD hRaw_DG
      refine QuarticSupportCone810.coneG ?_
      refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, hRaw_BG, quarticCmp_CG_of_zero hC0 hG, hRaw_DG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
    · by_cases hDGeq : 8 * D.natDegree = 5 * G.natDegree
      · -- G ties D
        have hEqRaw_GD : 5 * G.natDegree = 8 * D.natDegree := hDGeq.symm
        refine QuarticSupportCone810.coneDG ?_
        refine ⟨hD, hG, hEqRaw_GD, quarticCmp_AD_of_zero hA0 hD, hRaw_BD, quarticCmp_CD_of_zero hC0 hD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_FD_of_zero hF0 hD⟩
      · -- D strictly outranks G
        have hRed_GD : 5 * G.natDegree < 8 * D.natDegree := quarticScore_not_lt_not_eq hDGlt hDGeq
        have hRaw_GD : 5 * G.natDegree < 8 * D.natDegree := hRed_GD
        refine QuarticSupportCone810.coneD ?_
        refine ⟨hD, quarticCmp_AD_of_zero hA0 hD, hRaw_BD, quarticCmp_CD_of_zero hC0 hD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_FD_of_zero hF0 hD, hRaw_GD⟩
  · by_cases hBDeq : 5 * B.natDegree = 3 * D.natDegree
    · -- D ties B
      have hEqRaw_DB : 3 * D.natDegree = 5 * B.natDegree := hBDeq.symm
      by_cases hBGlt : 8 * B.natDegree < 3 * G.natDegree
      · -- G strictly outranks BD
        have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := hBGlt
        have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_eq_lt_DBG hEqRaw_DB hRaw_BG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, hRaw_BG, quarticCmp_CG_of_zero hC0 hG, hRaw_DG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
      · by_cases hBGeq : 8 * B.natDegree = 3 * G.natDegree
        · -- G ties BD
          have hEqRaw_GB : 3 * G.natDegree = 8 * B.natDegree := hBGeq.symm
          refine QuarticSupportCone810.coneBDG ?_
          refine ⟨hB, hD, hG, hEqRaw_DB, hEqRaw_GB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_FB_of_zero hF0 hB⟩
        · -- BD strictly outranks G
          have hRed_GB : 3 * G.natDegree < 8 * B.natDegree := quarticScore_not_lt_not_eq hBGlt hBGeq
          have hRaw_GB : 3 * G.natDegree < 8 * B.natDegree := hRed_GB
          refine QuarticSupportCone810.coneBD ?_
          refine ⟨hB, hD, hEqRaw_DB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_FB_of_zero hF0 hB, hRaw_GB⟩
    · -- B strictly outranks D
      have hRed_DB : 3 * D.natDegree < 5 * B.natDegree := quarticScore_not_lt_not_eq hBDlt hBDeq
      have hRaw_DB : 3 * D.natDegree < 5 * B.natDegree := hRed_DB
      by_cases hBGlt : 8 * B.natDegree < 3 * G.natDegree
      · -- G strictly outranks B
        have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := hBGlt
        have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DBG hRaw_DB hRaw_BG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, hRaw_BG, quarticCmp_CG_of_zero hC0 hG, hRaw_DG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
      · by_cases hBGeq : 8 * B.natDegree = 3 * G.natDegree
        · -- G ties B
          have hEqRaw_GB : 3 * G.natDegree = 8 * B.natDegree := hBGeq.symm
          refine QuarticSupportCone810.coneBG ?_
          refine ⟨hB, hG, hEqRaw_GB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, hRaw_DB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_FB_of_zero hF0 hB⟩
        · -- B strictly outranks G
          have hRed_GB : 3 * G.natDegree < 8 * B.natDegree := quarticScore_not_lt_not_eq hBGlt hBGeq
          have hRaw_GB : 3 * G.natDegree < 8 * B.natDegree := hRed_GB
          refine QuarticSupportCone810.coneB ?_
          refine ⟨hB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, hRaw_DB, quarticCmp_EB_of_zero hE0 hB, quarticCmp_FB_of_zero hF0 hB, hRaw_GB⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_BEF
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB : 0 < B.natDegree)
    (hC0 : C.natDegree = 0)
    (hD0 : D.natDegree = 0)
    (hE : 0 < E.natDegree)
    (hF : 0 < F.natDegree)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hBElt : 2 * B.natDegree < E.natDegree
  · -- E strictly outranks B
    have hRaw_BE : 6 * B.natDegree < 3 * E.natDegree := quarticCmp_BE_to_raw hBElt
    by_cases hEFlt : 7 * E.natDegree < 6 * F.natDegree
    · -- F strictly outranks E
      have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := hEFlt
      have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BEF hRaw_BE hRaw_EF
      refine QuarticSupportCone810.coneF ?_
      refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, hRaw_BF, quarticCmp_CF_of_zero hC0 hF, quarticCmp_DF_of_zero hD0 hF, hRaw_EF, quarticCmp_GF_of_zero hG0 hF⟩
    · by_cases hEFeq : 7 * E.natDegree = 6 * F.natDegree
      · -- F ties E
        have hEqRaw_FE : 6 * F.natDegree = 7 * E.natDegree := hEFeq.symm
        refine QuarticSupportCone810.coneEF ?_
        refine ⟨hE, hF, hEqRaw_FE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_zero hC0 hE, quarticCmp_DE_of_zero hD0 hE, quarticCmp_GE_of_zero hG0 hE⟩
      · -- E strictly outranks F
        have hRed_FE : 6 * F.natDegree < 7 * E.natDegree := quarticScore_not_lt_not_eq hEFlt hEFeq
        have hRaw_FE : 6 * F.natDegree < 7 * E.natDegree := hRed_FE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_zero hC0 hE, quarticCmp_DE_of_zero hD0 hE, hRaw_FE, quarticCmp_GE_of_zero hG0 hE⟩
  · by_cases hBEeq : 2 * B.natDegree = E.natDegree
    · -- E ties B
      have hEqRaw_EB : 3 * E.natDegree = 6 * B.natDegree := quarticEq_EB_to_raw (hBEeq.symm)
      by_cases hBFlt : 7 * B.natDegree < 3 * F.natDegree
      · -- F strictly outranks BE
        have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := hBFlt
        have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_eq_lt_EBF hEqRaw_EB hRaw_BF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, hRaw_BF, quarticCmp_CF_of_zero hC0 hF, quarticCmp_DF_of_zero hD0 hF, hRaw_EF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hBFeq : 7 * B.natDegree = 3 * F.natDegree
        · -- F ties BE
          have hEqRaw_FB : 3 * F.natDegree = 7 * B.natDegree := hBFeq.symm
          refine QuarticSupportCone810.coneBEF ?_
          refine ⟨hB, hE, hF, quarticEq_EB_of_raw hEqRaw_EB, hEqRaw_FB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_GB_of_zero hG0 hB⟩
        · -- BE strictly outranks F
          have hRed_FB : 3 * F.natDegree < 7 * B.natDegree := quarticScore_not_lt_not_eq hBFlt hBFeq
          have hRaw_FB : 3 * F.natDegree < 7 * B.natDegree := hRed_FB
          refine QuarticSupportCone810.coneBE ?_
          refine ⟨hB, hE, quarticEq_EB_of_raw hEqRaw_EB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_DB_of_zero hD0 hB, hRaw_FB, quarticCmp_GB_of_zero hG0 hB⟩
    · -- B strictly outranks E
      have hRed_EB : E.natDegree < 2 * B.natDegree := quarticScore_not_lt_not_eq hBElt hBEeq
      have hRaw_EB : 3 * E.natDegree < 6 * B.natDegree := quarticCmp_EB_to_raw hRed_EB
      by_cases hBFlt : 7 * B.natDegree < 3 * F.natDegree
      · -- F strictly outranks B
        have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := hBFlt
        have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_lt_trans_EBF hRaw_EB hRaw_BF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, hRaw_BF, quarticCmp_CF_of_zero hC0 hF, quarticCmp_DF_of_zero hD0 hF, hRaw_EF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hBFeq : 7 * B.natDegree = 3 * F.natDegree
        · -- F ties B
          have hEqRaw_FB : 3 * F.natDegree = 7 * B.natDegree := hBFeq.symm
          refine QuarticSupportCone810.coneBF ?_
          refine ⟨hB, hF, hEqRaw_FB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_raw hRaw_EB, quarticCmp_GB_of_zero hG0 hB⟩
        · -- B strictly outranks F
          have hRed_FB : 3 * F.natDegree < 7 * B.natDegree := quarticScore_not_lt_not_eq hBFlt hBFeq
          have hRaw_FB : 3 * F.natDegree < 7 * B.natDegree := hRed_FB
          refine QuarticSupportCone810.coneB ?_
          refine ⟨hB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_raw hRaw_EB, hRaw_FB, quarticCmp_GB_of_zero hG0 hB⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_BEG
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB : 0 < B.natDegree)
    (hC0 : C.natDegree = 0)
    (hD0 : D.natDegree = 0)
    (hE : 0 < E.natDegree)
    (hF0 : F.natDegree = 0)
    (hG : 0 < G.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hBElt : 2 * B.natDegree < E.natDegree
  · -- E strictly outranks B
    have hRaw_BE : 6 * B.natDegree < 3 * E.natDegree := quarticCmp_BE_to_raw hBElt
    by_cases hEGlt : 4 * E.natDegree < 3 * G.natDegree
    · -- G strictly outranks E
      have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticCmp_EG_to_raw hEGlt
      have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BEG hRaw_BE hRaw_EG
      refine QuarticSupportCone810.coneG ?_
      refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, hRaw_BG, quarticCmp_CG_of_zero hC0 hG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_raw hRaw_EG, quarticCmp_FG_of_zero hF0 hG⟩
    · by_cases hEGeq : 4 * E.natDegree = 3 * G.natDegree
      · -- G ties E
        have hEqRaw_GE : 6 * G.natDegree = 8 * E.natDegree := quarticEq_GE_to_raw (hEGeq.symm)
        refine QuarticSupportCone810.coneEG ?_
        refine ⟨hE, hG, quarticEq_GE_of_raw hEqRaw_GE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_zero hC0 hE, quarticCmp_DE_of_zero hD0 hE, quarticCmp_FE_of_zero hF0 hE⟩
      · -- E strictly outranks G
        have hRed_GE : 3 * G.natDegree < 4 * E.natDegree := quarticScore_not_lt_not_eq hEGlt hEGeq
        have hRaw_GE : 6 * G.natDegree < 8 * E.natDegree := quarticCmp_GE_to_raw hRed_GE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_zero hC0 hE, quarticCmp_DE_of_zero hD0 hE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_raw hRaw_GE⟩
  · by_cases hBEeq : 2 * B.natDegree = E.natDegree
    · -- E ties B
      have hEqRaw_EB : 3 * E.natDegree = 6 * B.natDegree := quarticEq_EB_to_raw (hBEeq.symm)
      by_cases hBGlt : 8 * B.natDegree < 3 * G.natDegree
      · -- G strictly outranks BE
        have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := hBGlt
        have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_eq_lt_EBG hEqRaw_EB hRaw_BG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, hRaw_BG, quarticCmp_CG_of_zero hC0 hG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_raw hRaw_EG, quarticCmp_FG_of_zero hF0 hG⟩
      · by_cases hBGeq : 8 * B.natDegree = 3 * G.natDegree
        · -- G ties BE
          have hEqRaw_GB : 3 * G.natDegree = 8 * B.natDegree := hBGeq.symm
          refine QuarticSupportCone810.coneBEG ?_
          refine ⟨hB, hE, hG, quarticEq_EB_of_raw hEqRaw_EB, hEqRaw_GB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_FB_of_zero hF0 hB⟩
        · -- BE strictly outranks G
          have hRed_GB : 3 * G.natDegree < 8 * B.natDegree := quarticScore_not_lt_not_eq hBGlt hBGeq
          have hRaw_GB : 3 * G.natDegree < 8 * B.natDegree := hRed_GB
          refine QuarticSupportCone810.coneBE ?_
          refine ⟨hB, hE, quarticEq_EB_of_raw hEqRaw_EB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_FB_of_zero hF0 hB, hRaw_GB⟩
    · -- B strictly outranks E
      have hRed_EB : E.natDegree < 2 * B.natDegree := quarticScore_not_lt_not_eq hBElt hBEeq
      have hRaw_EB : 3 * E.natDegree < 6 * B.natDegree := quarticCmp_EB_to_raw hRed_EB
      by_cases hBGlt : 8 * B.natDegree < 3 * G.natDegree
      · -- G strictly outranks B
        have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := hBGlt
        have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EBG hRaw_EB hRaw_BG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, hRaw_BG, quarticCmp_CG_of_zero hC0 hG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_raw hRaw_EG, quarticCmp_FG_of_zero hF0 hG⟩
      · by_cases hBGeq : 8 * B.natDegree = 3 * G.natDegree
        · -- G ties B
          have hEqRaw_GB : 3 * G.natDegree = 8 * B.natDegree := hBGeq.symm
          refine QuarticSupportCone810.coneBG ?_
          refine ⟨hB, hG, hEqRaw_GB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_raw hRaw_EB, quarticCmp_FB_of_zero hF0 hB⟩
        · -- B strictly outranks G
          have hRed_GB : 3 * G.natDegree < 8 * B.natDegree := quarticScore_not_lt_not_eq hBGlt hBGeq
          have hRaw_GB : 3 * G.natDegree < 8 * B.natDegree := hRed_GB
          refine QuarticSupportCone810.coneB ?_
          refine ⟨hB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_raw hRaw_EB, quarticCmp_FB_of_zero hF0 hB, hRaw_GB⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_BFG
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB : 0 < B.natDegree)
    (hC0 : C.natDegree = 0)
    (hD0 : D.natDegree = 0)
    (hE0 : E.natDegree = 0)
    (hF : 0 < F.natDegree)
    (hG : 0 < G.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hBFlt : 7 * B.natDegree < 3 * F.natDegree
  · -- F strictly outranks B
    have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := hBFlt
    by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
    · -- G strictly outranks F
      have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
      have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
      refine QuarticSupportCone810.coneG ?_
      refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, hRaw_BG, quarticCmp_CG_of_zero hC0 hG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_zero hE0 hG, hRaw_FG⟩
    · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
      · -- G ties F
        have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
        refine QuarticSupportCone810.coneFG ?_
        refine ⟨hF, hG, hEqRaw_GF, quarticCmp_AF_of_zero hA0 hF, hRaw_BF, quarticCmp_CF_of_zero hC0 hF, quarticCmp_DF_of_zero hD0 hF, quarticCmp_EF_of_zero hE0 hF⟩
      · -- F strictly outranks G
        have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
        have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, hRaw_BF, quarticCmp_CF_of_zero hC0 hF, quarticCmp_DF_of_zero hD0 hF, quarticCmp_EF_of_zero hE0 hF, hRaw_GF⟩
  · by_cases hBFeq : 7 * B.natDegree = 3 * F.natDegree
    · -- F ties B
      have hEqRaw_FB : 3 * F.natDegree = 7 * B.natDegree := hBFeq.symm
      by_cases hBGlt : 8 * B.natDegree < 3 * G.natDegree
      · -- G strictly outranks BF
        have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := hBGlt
        have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FBG hEqRaw_FB hRaw_BG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, hRaw_BG, quarticCmp_CG_of_zero hC0 hG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_zero hE0 hG, hRaw_FG⟩
      · by_cases hBGeq : 8 * B.natDegree = 3 * G.natDegree
        · -- G ties BF
          have hEqRaw_GB : 3 * G.natDegree = 8 * B.natDegree := hBGeq.symm
          refine QuarticSupportCone810.coneBFG ?_
          refine ⟨hB, hF, hG, hEqRaw_FB, hEqRaw_GB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_zero hE0 hB⟩
        · -- BF strictly outranks G
          have hRed_GB : 3 * G.natDegree < 8 * B.natDegree := quarticScore_not_lt_not_eq hBGlt hBGeq
          have hRaw_GB : 3 * G.natDegree < 8 * B.natDegree := hRed_GB
          refine QuarticSupportCone810.coneBF ?_
          refine ⟨hB, hF, hEqRaw_FB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_zero hE0 hB, hRaw_GB⟩
    · -- B strictly outranks F
      have hRed_FB : 3 * F.natDegree < 7 * B.natDegree := quarticScore_not_lt_not_eq hBFlt hBFeq
      have hRaw_FB : 3 * F.natDegree < 7 * B.natDegree := hRed_FB
      by_cases hBGlt : 8 * B.natDegree < 3 * G.natDegree
      · -- G strictly outranks B
        have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := hBGlt
        have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FBG hRaw_FB hRaw_BG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, hRaw_BG, quarticCmp_CG_of_zero hC0 hG, quarticCmp_DG_of_zero hD0 hG, quarticCmp_EG_of_zero hE0 hG, hRaw_FG⟩
      · by_cases hBGeq : 8 * B.natDegree = 3 * G.natDegree
        · -- G ties B
          have hEqRaw_GB : 3 * G.natDegree = 8 * B.natDegree := hBGeq.symm
          refine QuarticSupportCone810.coneBG ?_
          refine ⟨hB, hG, hEqRaw_GB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_zero hE0 hB, hRaw_FB⟩
        · -- B strictly outranks G
          have hRed_GB : 3 * G.natDegree < 8 * B.natDegree := quarticScore_not_lt_not_eq hBGlt hBGeq
          have hRaw_GB : 3 * G.natDegree < 8 * B.natDegree := hRed_GB
          refine QuarticSupportCone810.coneB ?_
          refine ⟨hB, quarticCmp_AB_of_zero hA0 hB, quarticCmp_CB_of_zero hC0 hB, quarticCmp_DB_of_zero hD0 hB, quarticCmp_EB_of_zero hE0 hB, hRaw_FB, hRaw_GB⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_CDE
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB0 : B.natDegree = 0)
    (hC : 0 < C.natDegree)
    (hD : 0 < D.natDegree)
    (hE : 0 < E.natDegree)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hCDlt : 5 * C.natDegree < 4 * D.natDegree
  · -- D strictly outranks C
    have hRaw_CD : 5 * C.natDegree < 4 * D.natDegree := hCDlt
    by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
    · -- E strictly outranks D
      have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := hDElt
      have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticScore_lt_trans_CDE hRaw_CD hRaw_DE
      refine QuarticSupportCone810.coneE ?_
      refine ⟨hE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
    · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
      · -- E ties D
        have hEqRaw_ED : 5 * E.natDegree = 6 * D.natDegree := hDEeq.symm
        refine QuarticSupportCone810.coneDE ?_
        refine ⟨hD, hE, hEqRaw_ED, quarticCmp_AD_of_zero hA0 hD, quarticCmp_BD_of_zero hB0 hD, hRaw_CD, quarticCmp_FD_of_zero hF0 hD, quarticCmp_GD_of_zero hG0 hD⟩
      · -- D strictly outranks E
        have hRed_ED : 5 * E.natDegree < 6 * D.natDegree := quarticScore_not_lt_not_eq hDElt hDEeq
        have hRaw_ED : 5 * E.natDegree < 6 * D.natDegree := hRed_ED
        refine QuarticSupportCone810.coneD ?_
        refine ⟨hD, quarticCmp_AD_of_zero hA0 hD, quarticCmp_BD_of_zero hB0 hD, hRaw_CD, hRaw_ED, quarticCmp_FD_of_zero hF0 hD, quarticCmp_GD_of_zero hG0 hD⟩
  · by_cases hCDeq : 5 * C.natDegree = 4 * D.natDegree
    · -- D ties C
      have hEqRaw_DC : 4 * D.natDegree = 5 * C.natDegree := hCDeq.symm
      by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
      · -- E strictly outranks CD
        have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticCmp_CE_to_raw hCElt
        have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := quarticScore_eq_lt_DCE hEqRaw_DC hRaw_CE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
      · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
        · -- E ties CD
          have hEqRaw_EC : 4 * E.natDegree = 6 * C.natDegree := quarticEq_EC_to_raw (hCEeq.symm)
          refine QuarticSupportCone810.coneCDE ?_
          refine ⟨hC, hD, hE, hEqRaw_DC, quarticEq_EC_of_raw hEqRaw_EC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_zero hG0 hC⟩
        · -- CD strictly outranks E
          have hRed_EC : 2 * E.natDegree < 3 * C.natDegree := quarticScore_not_lt_not_eq hCElt hCEeq
          have hRaw_EC : 4 * E.natDegree < 6 * C.natDegree := quarticCmp_EC_to_raw hRed_EC
          refine QuarticSupportCone810.coneCD ?_
          refine ⟨hC, hD, hEqRaw_DC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_EC_of_raw hRaw_EC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_zero hG0 hC⟩
    · -- C strictly outranks D
      have hRed_DC : 4 * D.natDegree < 5 * C.natDegree := quarticScore_not_lt_not_eq hCDlt hCDeq
      have hRaw_DC : 4 * D.natDegree < 5 * C.natDegree := hRed_DC
      by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
      · -- E strictly outranks C
        have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticCmp_CE_to_raw hCElt
        have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := quarticScore_lt_trans_DCE hRaw_DC hRaw_CE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, quarticCmp_FE_of_zero hF0 hE, quarticCmp_GE_of_zero hG0 hE⟩
      · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
        · -- E ties C
          have hEqRaw_EC : 4 * E.natDegree = 6 * C.natDegree := quarticEq_EC_to_raw (hCEeq.symm)
          refine QuarticSupportCone810.coneCE ?_
          refine ⟨hC, hE, quarticEq_EC_of_raw hEqRaw_EC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, hRaw_DC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_zero hG0 hC⟩
        · -- C strictly outranks E
          have hRed_EC : 2 * E.natDegree < 3 * C.natDegree := quarticScore_not_lt_not_eq hCElt hCEeq
          have hRaw_EC : 4 * E.natDegree < 6 * C.natDegree := quarticCmp_EC_to_raw hRed_EC
          refine QuarticSupportCone810.coneC ?_
          refine ⟨hC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, hRaw_DC, quarticCmp_EC_of_raw hRaw_EC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_zero hG0 hC⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_CDF
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB0 : B.natDegree = 0)
    (hC : 0 < C.natDegree)
    (hD : 0 < D.natDegree)
    (hE0 : E.natDegree = 0)
    (hF : 0 < F.natDegree)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hCDlt : 5 * C.natDegree < 4 * D.natDegree
  · -- D strictly outranks C
    have hRaw_CD : 5 * C.natDegree < 4 * D.natDegree := hCDlt
    by_cases hDFlt : 7 * D.natDegree < 5 * F.natDegree
    · -- F strictly outranks D
      have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := hDFlt
      have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CDF hRaw_CD hRaw_DF
      refine QuarticSupportCone810.coneF ?_
      refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, quarticCmp_BF_of_zero hB0 hF, hRaw_CF, hRaw_DF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
    · by_cases hDFeq : 7 * D.natDegree = 5 * F.natDegree
      · -- F ties D
        have hEqRaw_FD : 5 * F.natDegree = 7 * D.natDegree := hDFeq.symm
        refine QuarticSupportCone810.coneDF ?_
        refine ⟨hD, hF, hEqRaw_FD, quarticCmp_AD_of_zero hA0 hD, quarticCmp_BD_of_zero hB0 hD, hRaw_CD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_GD_of_zero hG0 hD⟩
      · -- D strictly outranks F
        have hRed_FD : 5 * F.natDegree < 7 * D.natDegree := quarticScore_not_lt_not_eq hDFlt hDFeq
        have hRaw_FD : 5 * F.natDegree < 7 * D.natDegree := hRed_FD
        refine QuarticSupportCone810.coneD ?_
        refine ⟨hD, quarticCmp_AD_of_zero hA0 hD, quarticCmp_BD_of_zero hB0 hD, hRaw_CD, quarticCmp_ED_of_zero hE0 hD, hRaw_FD, quarticCmp_GD_of_zero hG0 hD⟩
  · by_cases hCDeq : 5 * C.natDegree = 4 * D.natDegree
    · -- D ties C
      have hEqRaw_DC : 4 * D.natDegree = 5 * C.natDegree := hCDeq.symm
      by_cases hCFlt : 7 * C.natDegree < 4 * F.natDegree
      · -- F strictly outranks CD
        have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := hCFlt
        have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_eq_lt_DCF hEqRaw_DC hRaw_CF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, quarticCmp_BF_of_zero hB0 hF, hRaw_CF, hRaw_DF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hCFeq : 7 * C.natDegree = 4 * F.natDegree
        · -- F ties CD
          have hEqRaw_FC : 4 * F.natDegree = 7 * C.natDegree := hCFeq.symm
          refine QuarticSupportCone810.coneCDF ?_
          refine ⟨hC, hD, hF, hEqRaw_DC, hEqRaw_FC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_GC_of_zero hG0 hC⟩
        · -- CD strictly outranks F
          have hRed_FC : 4 * F.natDegree < 7 * C.natDegree := quarticScore_not_lt_not_eq hCFlt hCFeq
          have hRaw_FC : 4 * F.natDegree < 7 * C.natDegree := hRed_FC
          refine QuarticSupportCone810.coneCD ?_
          refine ⟨hC, hD, hEqRaw_DC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_EC_of_zero hE0 hC, hRaw_FC, quarticCmp_GC_of_zero hG0 hC⟩
    · -- C strictly outranks D
      have hRed_DC : 4 * D.natDegree < 5 * C.natDegree := quarticScore_not_lt_not_eq hCDlt hCDeq
      have hRaw_DC : 4 * D.natDegree < 5 * C.natDegree := hRed_DC
      by_cases hCFlt : 7 * C.natDegree < 4 * F.natDegree
      · -- F strictly outranks C
        have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := hCFlt
        have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_lt_trans_DCF hRaw_DC hRaw_CF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, quarticCmp_BF_of_zero hB0 hF, hRaw_CF, hRaw_DF, quarticCmp_EF_of_zero hE0 hF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hCFeq : 7 * C.natDegree = 4 * F.natDegree
        · -- F ties C
          have hEqRaw_FC : 4 * F.natDegree = 7 * C.natDegree := hCFeq.symm
          refine QuarticSupportCone810.coneCF ?_
          refine ⟨hC, hF, hEqRaw_FC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, hRaw_DC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_GC_of_zero hG0 hC⟩
        · -- C strictly outranks F
          have hRed_FC : 4 * F.natDegree < 7 * C.natDegree := quarticScore_not_lt_not_eq hCFlt hCFeq
          have hRaw_FC : 4 * F.natDegree < 7 * C.natDegree := hRed_FC
          refine QuarticSupportCone810.coneC ?_
          refine ⟨hC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, hRaw_DC, quarticCmp_EC_of_zero hE0 hC, hRaw_FC, quarticCmp_GC_of_zero hG0 hC⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_CDG
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB0 : B.natDegree = 0)
    (hC : 0 < C.natDegree)
    (hD : 0 < D.natDegree)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG : 0 < G.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hCDlt : 5 * C.natDegree < 4 * D.natDegree
  · -- D strictly outranks C
    have hRaw_CD : 5 * C.natDegree < 4 * D.natDegree := hCDlt
    by_cases hDGlt : 8 * D.natDegree < 5 * G.natDegree
    · -- G strictly outranks D
      have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := hDGlt
      have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CDG hRaw_CD hRaw_DG
      refine QuarticSupportCone810.coneG ?_
      refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
    · by_cases hDGeq : 8 * D.natDegree = 5 * G.natDegree
      · -- G ties D
        have hEqRaw_GD : 5 * G.natDegree = 8 * D.natDegree := hDGeq.symm
        refine QuarticSupportCone810.coneDG ?_
        refine ⟨hD, hG, hEqRaw_GD, quarticCmp_AD_of_zero hA0 hD, quarticCmp_BD_of_zero hB0 hD, hRaw_CD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_FD_of_zero hF0 hD⟩
      · -- D strictly outranks G
        have hRed_GD : 5 * G.natDegree < 8 * D.natDegree := quarticScore_not_lt_not_eq hDGlt hDGeq
        have hRaw_GD : 5 * G.natDegree < 8 * D.natDegree := hRed_GD
        refine QuarticSupportCone810.coneD ?_
        refine ⟨hD, quarticCmp_AD_of_zero hA0 hD, quarticCmp_BD_of_zero hB0 hD, hRaw_CD, quarticCmp_ED_of_zero hE0 hD, quarticCmp_FD_of_zero hF0 hD, hRaw_GD⟩
  · by_cases hCDeq : 5 * C.natDegree = 4 * D.natDegree
    · -- D ties C
      have hEqRaw_DC : 4 * D.natDegree = 5 * C.natDegree := hCDeq.symm
      by_cases hCGlt : 2 * C.natDegree < G.natDegree
      · -- G strictly outranks CD
        have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticCmp_CG_to_raw hCGlt
        have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_eq_lt_DCG hEqRaw_DC hRaw_CG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
      · by_cases hCGeq : 2 * C.natDegree = G.natDegree
        · -- G ties CD
          have hEqRaw_GC : 4 * G.natDegree = 8 * C.natDegree := quarticEq_GC_to_raw (hCGeq.symm)
          refine QuarticSupportCone810.coneCDG ?_
          refine ⟨hC, hD, hG, hEqRaw_DC, quarticEq_GC_of_raw hEqRaw_GC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_FC_of_zero hF0 hC⟩
        · -- CD strictly outranks G
          have hRed_GC : G.natDegree < 2 * C.natDegree := quarticScore_not_lt_not_eq hCGlt hCGeq
          have hRaw_GC : 4 * G.natDegree < 8 * C.natDegree := quarticCmp_GC_to_raw hRed_GC
          refine QuarticSupportCone810.coneCD ?_
          refine ⟨hC, hD, hEqRaw_DC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_raw hRaw_GC⟩
    · -- C strictly outranks D
      have hRed_DC : 4 * D.natDegree < 5 * C.natDegree := quarticScore_not_lt_not_eq hCDlt hCDeq
      have hRaw_DC : 4 * D.natDegree < 5 * C.natDegree := hRed_DC
      by_cases hCGlt : 2 * C.natDegree < G.natDegree
      · -- G strictly outranks C
        have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticCmp_CG_to_raw hCGlt
        have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DCG hRaw_DC hRaw_CG
        refine QuarticSupportCone810.coneG ?_
        refine ⟨hG, quarticCmp_AG_of_zero hA0 hG, quarticCmp_BG_of_zero hB0 hG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_zero hE0 hG, quarticCmp_FG_of_zero hF0 hG⟩
      · by_cases hCGeq : 2 * C.natDegree = G.natDegree
        · -- G ties C
          have hEqRaw_GC : 4 * G.natDegree = 8 * C.natDegree := quarticEq_GC_to_raw (hCGeq.symm)
          refine QuarticSupportCone810.coneCG ?_
          refine ⟨hC, hG, quarticEq_GC_of_raw hEqRaw_GC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, hRaw_DC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_FC_of_zero hF0 hC⟩
        · -- C strictly outranks G
          have hRed_GC : G.natDegree < 2 * C.natDegree := quarticScore_not_lt_not_eq hCGlt hCGeq
          have hRaw_GC : 4 * G.natDegree < 8 * C.natDegree := quarticCmp_GC_to_raw hRed_GC
          refine QuarticSupportCone810.coneC ?_
          refine ⟨hC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, hRaw_DC, quarticCmp_EC_of_zero hE0 hC, quarticCmp_FC_of_zero hF0 hC, quarticCmp_GC_of_raw hRaw_GC⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_CEF
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB0 : B.natDegree = 0)
    (hC : 0 < C.natDegree)
    (hD0 : D.natDegree = 0)
    (hE : 0 < E.natDegree)
    (hF : 0 < F.natDegree)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
  · -- E strictly outranks C
    have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticCmp_CE_to_raw hCElt
    by_cases hEFlt : 7 * E.natDegree < 6 * F.natDegree
    · -- F strictly outranks E
      have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := hEFlt
      have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CEF hRaw_CE hRaw_EF
      refine QuarticSupportCone810.coneF ?_
      refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, quarticCmp_BF_of_zero hB0 hF, hRaw_CF, quarticCmp_DF_of_zero hD0 hF, hRaw_EF, quarticCmp_GF_of_zero hG0 hF⟩
    · by_cases hEFeq : 7 * E.natDegree = 6 * F.natDegree
      · -- F ties E
        have hEqRaw_FE : 6 * F.natDegree = 7 * E.natDegree := hEFeq.symm
        refine QuarticSupportCone810.coneEF ?_
        refine ⟨hE, hF, hEqRaw_FE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_raw hRaw_CE, quarticCmp_DE_of_zero hD0 hE, quarticCmp_GE_of_zero hG0 hE⟩
      · -- E strictly outranks F
        have hRed_FE : 6 * F.natDegree < 7 * E.natDegree := quarticScore_not_lt_not_eq hEFlt hEFeq
        have hRaw_FE : 6 * F.natDegree < 7 * E.natDegree := hRed_FE
        refine QuarticSupportCone810.coneE ?_
        refine ⟨hE, quarticCmp_AE_of_zero hA0 hE, quarticCmp_BE_of_zero hB0 hE, quarticCmp_CE_of_raw hRaw_CE, quarticCmp_DE_of_zero hD0 hE, hRaw_FE, quarticCmp_GE_of_zero hG0 hE⟩
  · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
    · -- E ties C
      have hEqRaw_EC : 4 * E.natDegree = 6 * C.natDegree := quarticEq_EC_to_raw (hCEeq.symm)
      by_cases hCFlt : 7 * C.natDegree < 4 * F.natDegree
      · -- F strictly outranks CE
        have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := hCFlt
        have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_eq_lt_ECF hEqRaw_EC hRaw_CF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, quarticCmp_BF_of_zero hB0 hF, hRaw_CF, quarticCmp_DF_of_zero hD0 hF, hRaw_EF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hCFeq : 7 * C.natDegree = 4 * F.natDegree
        · -- F ties CE
          have hEqRaw_FC : 4 * F.natDegree = 7 * C.natDegree := hCFeq.symm
          refine QuarticSupportCone810.coneCEF ?_
          refine ⟨hC, hE, hF, quarticEq_EC_of_raw hEqRaw_EC, hEqRaw_FC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_GC_of_zero hG0 hC⟩
        · -- CE strictly outranks F
          have hRed_FC : 4 * F.natDegree < 7 * C.natDegree := quarticScore_not_lt_not_eq hCFlt hCFeq
          have hRaw_FC : 4 * F.natDegree < 7 * C.natDegree := hRed_FC
          refine QuarticSupportCone810.coneCE ?_
          refine ⟨hC, hE, quarticEq_EC_of_raw hEqRaw_EC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_DC_of_zero hD0 hC, hRaw_FC, quarticCmp_GC_of_zero hG0 hC⟩
    · -- C strictly outranks E
      have hRed_EC : 2 * E.natDegree < 3 * C.natDegree := quarticScore_not_lt_not_eq hCElt hCEeq
      have hRaw_EC : 4 * E.natDegree < 6 * C.natDegree := quarticCmp_EC_to_raw hRed_EC
      by_cases hCFlt : 7 * C.natDegree < 4 * F.natDegree
      · -- F strictly outranks C
        have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := hCFlt
        have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_lt_trans_ECF hRaw_EC hRaw_CF
        refine QuarticSupportCone810.coneF ?_
        refine ⟨hF, quarticCmp_AF_of_zero hA0 hF, quarticCmp_BF_of_zero hB0 hF, hRaw_CF, quarticCmp_DF_of_zero hD0 hF, hRaw_EF, quarticCmp_GF_of_zero hG0 hF⟩
      · by_cases hCFeq : 7 * C.natDegree = 4 * F.natDegree
        · -- F ties C
          have hEqRaw_FC : 4 * F.natDegree = 7 * C.natDegree := hCFeq.symm
          refine QuarticSupportCone810.coneCF ?_
          refine ⟨hC, hF, hEqRaw_FC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_EC_of_raw hRaw_EC, quarticCmp_GC_of_zero hG0 hC⟩
        · -- C strictly outranks F
          have hRed_FC : 4 * F.natDegree < 7 * C.natDegree := quarticScore_not_lt_not_eq hCFlt hCFeq
          have hRaw_FC : 4 * F.natDegree < 7 * C.natDegree := hRed_FC
          refine QuarticSupportCone810.coneC ?_
          refine ⟨hC, quarticCmp_AC_of_zero hA0 hC, quarticCmp_BC_of_zero hB0 hC, quarticCmp_DC_of_zero hD0 hC, quarticCmp_EC_of_raw hRaw_EC, hRaw_FC, quarticCmp_GC_of_zero hG0 hC⟩

end QuarticExhaust810

end Max11DegreeRoutes
