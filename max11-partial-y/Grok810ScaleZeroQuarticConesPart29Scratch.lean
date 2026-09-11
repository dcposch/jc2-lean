import Grok810ScaleZeroQuarticConesPart22Scratch
import Grok810ScaleZeroQuarticConesPart23Scratch
import Grok810ScaleZeroQuarticConesPart24Scratch
import Grok810ScaleZeroQuarticConesPart25Scratch
import Grok810ScaleZeroQuarticConesPart26Scratch
import Grok810ScaleZeroQuarticConesPart28Scratch

/-! # Part 29 of `Grok810ScaleZeroQuarticConesScratch`.

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
theorem quarticSupportCone810_of_live_ABCDEFG_cand_AB_rest_CDEFG
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB : 0 < B.natDegree)
    (hC : 0 < C.natDegree)
    (hD : 0 < D.natDegree)
    (hE : 0 < E.natDegree)
    (hF : 0 < F.natDegree)
    (hG : 0 < G.natDegree)
    (hEqRaw_BA : 2 * B.natDegree = 3 * A.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hAClt : 2 * A.natDegree < C.natDegree
  · -- C strictly outranks AB
    have hRaw_AC : 4 * A.natDegree < 2 * C.natDegree := quarticCmp_AC_to_raw hAClt
    have hRaw_BC : 4 * B.natDegree < 3 * C.natDegree := quarticScore_eq_lt_BAC hEqRaw_BA hRaw_AC
    exact quarticSupportCone810_of_live_ABCDEFG_cand_C_rest_DEFG A B C D E F G hA hB hC hD hE hF hG hRaw_AC hRaw_BC
  · by_cases hACeq : 2 * A.natDegree = C.natDegree
    · -- C ties AB
      have hEqRaw_CA : 2 * C.natDegree = 4 * A.natDegree := quarticEq_CA_to_raw (hACeq.symm)
      exact quarticSupportCone810_of_live_ABCDEFG_cand_ABC_rest_DEFG A B C D E F G hA hB hC hD hE hF hG hEqRaw_BA hEqRaw_CA
    · -- AB strictly outranks C
      have hRed_CA : C.natDegree < 2 * A.natDegree := quarticScore_not_lt_not_eq hAClt hACeq
      have hRaw_CA : 2 * C.natDegree < 4 * A.natDegree := quarticCmp_CA_to_raw hRed_CA
      exact quarticSupportCone810_of_live_ABCDEFG_cand_AB_rest_DEFG A B C D E F G hA hB hC hD hE hF hG hRaw_CA hEqRaw_BA

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_ABCDEFG_cand_AC_rest_DEFG
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB : 0 < B.natDegree)
    (hC : 0 < C.natDegree)
    (hD : 0 < D.natDegree)
    (hE : 0 < E.natDegree)
    (hF : 0 < F.natDegree)
    (hG : 0 < G.natDegree)
    (hRaw_BA : 2 * B.natDegree < 3 * A.natDegree)
    (hEqRaw_CA : 2 * C.natDegree = 4 * A.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
  · -- D strictly outranks AC
    have hRaw_AD : 5 * A.natDegree < 2 * D.natDegree := hADlt
    have hRaw_CD : 5 * C.natDegree < 4 * D.natDegree := quarticScore_eq_lt_CAD hEqRaw_CA hRaw_AD
    have hRaw_BD : 5 * B.natDegree < 3 * D.natDegree := quarticScore_lt_trans_BAD hRaw_BA hRaw_AD
    by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
    · -- E strictly outranks D
      have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := hDElt
      have hRaw_AE : 6 * A.natDegree < 2 * E.natDegree := quarticScore_lt_trans_ADE hRaw_AD hRaw_DE
      have hRaw_BE : 6 * B.natDegree < 3 * E.natDegree := quarticScore_lt_trans_BDE hRaw_BD hRaw_DE
      have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticScore_lt_trans_CDE hRaw_CD hRaw_DE
      by_cases hEFlt : 7 * E.natDegree < 6 * F.natDegree
      · -- F strictly outranks E
        have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := hEFlt
        have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := quarticScore_lt_trans_AEF hRaw_AE hRaw_EF
        have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BEF hRaw_BE hRaw_EF
        have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CEF hRaw_CE hRaw_EF
        have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_lt_trans_DEF hRaw_DE hRaw_EF
        by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
        · -- G strictly outranks F
          have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
          have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
          have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
          have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
          have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
          have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
          refine QuarticSupportCone810.coneG ?_
          refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
        · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
          · -- G ties F
            have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
            refine QuarticSupportCone810.coneFG ?_
            refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
          · -- F strictly outranks G
            have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
            have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
            refine QuarticSupportCone810.coneF ?_
            refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
      · by_cases hEFeq : 7 * E.natDegree = 6 * F.natDegree
        · -- F ties E
          have hEqRaw_FE : 6 * F.natDegree = 7 * E.natDegree := hEFeq.symm
          by_cases hEGlt : 4 * E.natDegree < 3 * G.natDegree
          · -- G strictly outranks EF
            have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticCmp_EG_to_raw hEGlt
            have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FEG hEqRaw_FE hRaw_EG
            have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AEG hRaw_AE hRaw_EG
            have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BEG hRaw_BE hRaw_EG
            have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CEG hRaw_CE hRaw_EG
            have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DEG hRaw_DE hRaw_EG
            refine QuarticSupportCone810.coneG ?_
            refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
          · by_cases hEGeq : 4 * E.natDegree = 3 * G.natDegree
            · -- G ties EF
              have hEqRaw_GE : 6 * G.natDegree = 8 * E.natDegree := quarticEq_GE_to_raw (hEGeq.symm)
              refine QuarticSupportCone810.coneEFG ?_
              refine ⟨hE, hF, hG, hEqRaw_FE, quarticEq_GE_of_raw hEqRaw_GE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE⟩
            · -- EF strictly outranks G
              have hRed_GE : 3 * G.natDegree < 4 * E.natDegree := quarticScore_not_lt_not_eq hEGlt hEGeq
              have hRaw_GE : 6 * G.natDegree < 8 * E.natDegree := quarticCmp_GE_to_raw hRed_GE
              refine QuarticSupportCone810.coneEF ?_
              refine ⟨hE, hF, hEqRaw_FE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, quarticCmp_GE_of_raw hRaw_GE⟩
        · -- E strictly outranks F
          have hRed_FE : 6 * F.natDegree < 7 * E.natDegree := quarticScore_not_lt_not_eq hEFlt hEFeq
          have hRaw_FE : 6 * F.natDegree < 7 * E.natDegree := hRed_FE
          by_cases hEGlt : 4 * E.natDegree < 3 * G.natDegree
          · -- G strictly outranks E
            have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticCmp_EG_to_raw hEGlt
            have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AEG hRaw_AE hRaw_EG
            have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BEG hRaw_BE hRaw_EG
            have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CEG hRaw_CE hRaw_EG
            have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DEG hRaw_DE hRaw_EG
            have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FEG hRaw_FE hRaw_EG
            refine QuarticSupportCone810.coneG ?_
            refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
          · by_cases hEGeq : 4 * E.natDegree = 3 * G.natDegree
            · -- G ties E
              have hEqRaw_GE : 6 * G.natDegree = 8 * E.natDegree := quarticEq_GE_to_raw (hEGeq.symm)
              refine QuarticSupportCone810.coneEG ?_
              refine ⟨hE, hG, quarticEq_GE_of_raw hEqRaw_GE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, hRaw_FE⟩
            · -- E strictly outranks G
              have hRed_GE : 3 * G.natDegree < 4 * E.natDegree := quarticScore_not_lt_not_eq hEGlt hEGeq
              have hRaw_GE : 6 * G.natDegree < 8 * E.natDegree := quarticCmp_GE_to_raw hRed_GE
              refine QuarticSupportCone810.coneE ?_
              refine ⟨hE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, hRaw_FE, quarticCmp_GE_of_raw hRaw_GE⟩
    · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
      · -- E ties D
        have hEqRaw_ED : 5 * E.natDegree = 6 * D.natDegree := hDEeq.symm
        by_cases hDFlt : 7 * D.natDegree < 5 * F.natDegree
        · -- F strictly outranks DE
          have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := hDFlt
          have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_eq_lt_EDF hEqRaw_ED hRaw_DF
          have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := quarticScore_lt_trans_ADF hRaw_AD hRaw_DF
          have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BDF hRaw_BD hRaw_DF
          have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CDF hRaw_CD hRaw_DF
          by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
          · -- G strictly outranks F
            have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
            have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
            have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
            have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
            have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
            have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
            refine QuarticSupportCone810.coneG ?_
            refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
          · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
            · -- G ties F
              have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
              refine QuarticSupportCone810.coneFG ?_
              refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
            · -- F strictly outranks G
              have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
              have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
              refine QuarticSupportCone810.coneF ?_
              refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
        · by_cases hDFeq : 7 * D.natDegree = 5 * F.natDegree
          · -- F ties DE
            have hEqRaw_FD : 5 * F.natDegree = 7 * D.natDegree := hDFeq.symm
            by_cases hDGlt : 8 * D.natDegree < 5 * G.natDegree
            · -- G strictly outranks DEF
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := hDGlt
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_eq_lt_EDG hEqRaw_ED hRaw_DG
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FDG hEqRaw_FD hRaw_DG
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_ADG hRaw_AD hRaw_DG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BDG hRaw_BD hRaw_DG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CDG hRaw_CD hRaw_DG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hDGeq : 8 * D.natDegree = 5 * G.natDegree
              · -- G ties DEF
                have hEqRaw_GD : 5 * G.natDegree = 8 * D.natDegree := hDGeq.symm
                refine QuarticSupportCone810.coneDEFG ?_
                refine ⟨hD, hE, hF, hG, hEqRaw_ED, hEqRaw_FD, hEqRaw_GD, hRaw_AD, hRaw_BD, hRaw_CD⟩
              · -- DEF strictly outranks G
                have hRed_GD : 5 * G.natDegree < 8 * D.natDegree := quarticScore_not_lt_not_eq hDGlt hDGeq
                have hRaw_GD : 5 * G.natDegree < 8 * D.natDegree := hRed_GD
                refine QuarticSupportCone810.coneDEF ?_
                refine ⟨hD, hE, hF, hEqRaw_ED, hEqRaw_FD, hRaw_AD, hRaw_BD, hRaw_CD, hRaw_GD⟩
          · -- DE strictly outranks F
            have hRed_FD : 5 * F.natDegree < 7 * D.natDegree := quarticScore_not_lt_not_eq hDFlt hDFeq
            have hRaw_FD : 5 * F.natDegree < 7 * D.natDegree := hRed_FD
            by_cases hDGlt : 8 * D.natDegree < 5 * G.natDegree
            · -- G strictly outranks DE
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := hDGlt
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_eq_lt_EDG hEqRaw_ED hRaw_DG
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_ADG hRaw_AD hRaw_DG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BDG hRaw_BD hRaw_DG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CDG hRaw_CD hRaw_DG
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FDG hRaw_FD hRaw_DG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hDGeq : 8 * D.natDegree = 5 * G.natDegree
              · -- G ties DE
                have hEqRaw_GD : 5 * G.natDegree = 8 * D.natDegree := hDGeq.symm
                refine QuarticSupportCone810.coneDEG ?_
                refine ⟨hD, hE, hG, hEqRaw_ED, hEqRaw_GD, hRaw_AD, hRaw_BD, hRaw_CD, hRaw_FD⟩
              · -- DE strictly outranks G
                have hRed_GD : 5 * G.natDegree < 8 * D.natDegree := quarticScore_not_lt_not_eq hDGlt hDGeq
                have hRaw_GD : 5 * G.natDegree < 8 * D.natDegree := hRed_GD
                refine QuarticSupportCone810.coneDE ?_
                refine ⟨hD, hE, hEqRaw_ED, hRaw_AD, hRaw_BD, hRaw_CD, hRaw_FD, hRaw_GD⟩
      · -- D strictly outranks E
        have hRed_ED : 5 * E.natDegree < 6 * D.natDegree := quarticScore_not_lt_not_eq hDElt hDEeq
        have hRaw_ED : 5 * E.natDegree < 6 * D.natDegree := hRed_ED
        by_cases hDFlt : 7 * D.natDegree < 5 * F.natDegree
        · -- F strictly outranks D
          have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := hDFlt
          have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := quarticScore_lt_trans_ADF hRaw_AD hRaw_DF
          have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BDF hRaw_BD hRaw_DF
          have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CDF hRaw_CD hRaw_DF
          have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_lt_trans_EDF hRaw_ED hRaw_DF
          by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
          · -- G strictly outranks F
            have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
            have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
            have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
            have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
            have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
            have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
            refine QuarticSupportCone810.coneG ?_
            refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
          · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
            · -- G ties F
              have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
              refine QuarticSupportCone810.coneFG ?_
              refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
            · -- F strictly outranks G
              have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
              have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
              refine QuarticSupportCone810.coneF ?_
              refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
        · by_cases hDFeq : 7 * D.natDegree = 5 * F.natDegree
          · -- F ties D
            have hEqRaw_FD : 5 * F.natDegree = 7 * D.natDegree := hDFeq.symm
            by_cases hDGlt : 8 * D.natDegree < 5 * G.natDegree
            · -- G strictly outranks DF
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := hDGlt
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FDG hEqRaw_FD hRaw_DG
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_ADG hRaw_AD hRaw_DG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BDG hRaw_BD hRaw_DG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CDG hRaw_CD hRaw_DG
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EDG hRaw_ED hRaw_DG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hDGeq : 8 * D.natDegree = 5 * G.natDegree
              · -- G ties DF
                have hEqRaw_GD : 5 * G.natDegree = 8 * D.natDegree := hDGeq.symm
                refine QuarticSupportCone810.coneDFG ?_
                refine ⟨hD, hF, hG, hEqRaw_FD, hEqRaw_GD, hRaw_AD, hRaw_BD, hRaw_CD, hRaw_ED⟩
              · -- DF strictly outranks G
                have hRed_GD : 5 * G.natDegree < 8 * D.natDegree := quarticScore_not_lt_not_eq hDGlt hDGeq
                have hRaw_GD : 5 * G.natDegree < 8 * D.natDegree := hRed_GD
                refine QuarticSupportCone810.coneDF ?_
                refine ⟨hD, hF, hEqRaw_FD, hRaw_AD, hRaw_BD, hRaw_CD, hRaw_ED, hRaw_GD⟩
          · -- D strictly outranks F
            have hRed_FD : 5 * F.natDegree < 7 * D.natDegree := quarticScore_not_lt_not_eq hDFlt hDFeq
            have hRaw_FD : 5 * F.natDegree < 7 * D.natDegree := hRed_FD
            by_cases hDGlt : 8 * D.natDegree < 5 * G.natDegree
            · -- G strictly outranks D
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := hDGlt
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_ADG hRaw_AD hRaw_DG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BDG hRaw_BD hRaw_DG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CDG hRaw_CD hRaw_DG
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EDG hRaw_ED hRaw_DG
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FDG hRaw_FD hRaw_DG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hDGeq : 8 * D.natDegree = 5 * G.natDegree
              · -- G ties D
                have hEqRaw_GD : 5 * G.natDegree = 8 * D.natDegree := hDGeq.symm
                refine QuarticSupportCone810.coneDG ?_
                refine ⟨hD, hG, hEqRaw_GD, hRaw_AD, hRaw_BD, hRaw_CD, hRaw_ED, hRaw_FD⟩
              · -- D strictly outranks G
                have hRed_GD : 5 * G.natDegree < 8 * D.natDegree := quarticScore_not_lt_not_eq hDGlt hDGeq
                have hRaw_GD : 5 * G.natDegree < 8 * D.natDegree := hRed_GD
                refine QuarticSupportCone810.coneD ?_
                refine ⟨hD, hRaw_AD, hRaw_BD, hRaw_CD, hRaw_ED, hRaw_FD, hRaw_GD⟩
  · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
    · -- D ties AC
      have hEqRaw_DA : 2 * D.natDegree = 5 * A.natDegree := hADeq.symm
      by_cases hAElt : 3 * A.natDegree < E.natDegree
      · -- E strictly outranks ACD
        have hRaw_AE : 6 * A.natDegree < 2 * E.natDegree := quarticCmp_AE_to_raw hAElt
        have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticScore_eq_lt_CAE hEqRaw_CA hRaw_AE
        have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := quarticScore_eq_lt_DAE hEqRaw_DA hRaw_AE
        have hRaw_BE : 6 * B.natDegree < 3 * E.natDegree := quarticScore_lt_trans_BAE hRaw_BA hRaw_AE
        by_cases hEFlt : 7 * E.natDegree < 6 * F.natDegree
        · -- F strictly outranks E
          have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := hEFlt
          have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := quarticScore_lt_trans_AEF hRaw_AE hRaw_EF
          have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BEF hRaw_BE hRaw_EF
          have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CEF hRaw_CE hRaw_EF
          have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_lt_trans_DEF hRaw_DE hRaw_EF
          by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
          · -- G strictly outranks F
            have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
            have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
            have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
            have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
            have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
            have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
            refine QuarticSupportCone810.coneG ?_
            refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
          · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
            · -- G ties F
              have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
              refine QuarticSupportCone810.coneFG ?_
              refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
            · -- F strictly outranks G
              have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
              have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
              refine QuarticSupportCone810.coneF ?_
              refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
        · by_cases hEFeq : 7 * E.natDegree = 6 * F.natDegree
          · -- F ties E
            have hEqRaw_FE : 6 * F.natDegree = 7 * E.natDegree := hEFeq.symm
            by_cases hEGlt : 4 * E.natDegree < 3 * G.natDegree
            · -- G strictly outranks EF
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticCmp_EG_to_raw hEGlt
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FEG hEqRaw_FE hRaw_EG
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AEG hRaw_AE hRaw_EG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BEG hRaw_BE hRaw_EG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CEG hRaw_CE hRaw_EG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DEG hRaw_DE hRaw_EG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hEGeq : 4 * E.natDegree = 3 * G.natDegree
              · -- G ties EF
                have hEqRaw_GE : 6 * G.natDegree = 8 * E.natDegree := quarticEq_GE_to_raw (hEGeq.symm)
                refine QuarticSupportCone810.coneEFG ?_
                refine ⟨hE, hF, hG, hEqRaw_FE, quarticEq_GE_of_raw hEqRaw_GE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE⟩
              · -- EF strictly outranks G
                have hRed_GE : 3 * G.natDegree < 4 * E.natDegree := quarticScore_not_lt_not_eq hEGlt hEGeq
                have hRaw_GE : 6 * G.natDegree < 8 * E.natDegree := quarticCmp_GE_to_raw hRed_GE
                refine QuarticSupportCone810.coneEF ?_
                refine ⟨hE, hF, hEqRaw_FE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, quarticCmp_GE_of_raw hRaw_GE⟩
          · -- E strictly outranks F
            have hRed_FE : 6 * F.natDegree < 7 * E.natDegree := quarticScore_not_lt_not_eq hEFlt hEFeq
            have hRaw_FE : 6 * F.natDegree < 7 * E.natDegree := hRed_FE
            by_cases hEGlt : 4 * E.natDegree < 3 * G.natDegree
            · -- G strictly outranks E
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticCmp_EG_to_raw hEGlt
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AEG hRaw_AE hRaw_EG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BEG hRaw_BE hRaw_EG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CEG hRaw_CE hRaw_EG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DEG hRaw_DE hRaw_EG
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FEG hRaw_FE hRaw_EG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hEGeq : 4 * E.natDegree = 3 * G.natDegree
              · -- G ties E
                have hEqRaw_GE : 6 * G.natDegree = 8 * E.natDegree := quarticEq_GE_to_raw (hEGeq.symm)
                refine QuarticSupportCone810.coneEG ?_
                refine ⟨hE, hG, quarticEq_GE_of_raw hEqRaw_GE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, hRaw_FE⟩
              · -- E strictly outranks G
                have hRed_GE : 3 * G.natDegree < 4 * E.natDegree := quarticScore_not_lt_not_eq hEGlt hEGeq
                have hRaw_GE : 6 * G.natDegree < 8 * E.natDegree := quarticCmp_GE_to_raw hRed_GE
                refine QuarticSupportCone810.coneE ?_
                refine ⟨hE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, hRaw_FE, quarticCmp_GE_of_raw hRaw_GE⟩
      · by_cases hAEeq : 3 * A.natDegree = E.natDegree
        · -- E ties ACD
          have hEqRaw_EA : 2 * E.natDegree = 6 * A.natDegree := quarticEq_EA_to_raw (hAEeq.symm)
          by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
          · -- F strictly outranks ACDE
            have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
            have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_eq_lt_CAF hEqRaw_CA hRaw_AF
            have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_eq_lt_DAF hEqRaw_DA hRaw_AF
            have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_eq_lt_EAF hEqRaw_EA hRaw_AF
            have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BAF hRaw_BA hRaw_AF
            by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
            · -- G strictly outranks F
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
              · -- G ties F
                have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
                refine QuarticSupportCone810.coneFG ?_
                refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
              · -- F strictly outranks G
                have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
                have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
                refine QuarticSupportCone810.coneF ?_
                refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
          · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
            · -- F ties ACDE
              have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks ACDEF
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_eq_lt_CAG hEqRaw_CA hRaw_AG
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_eq_lt_DAG hEqRaw_DA hRaw_AG
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_eq_lt_EAG hEqRaw_EA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FAG hEqRaw_FA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties ACDEF
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneACDEFG ?_
                  refine ⟨hA, hC, hD, hE, hF, hG, quarticEq_CA_of_raw hEqRaw_CA, hEqRaw_DA, quarticEq_EA_of_raw hEqRaw_EA, hEqRaw_FA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA⟩
                · -- ACDEF strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneACDEF ?_
                  refine ⟨hA, hC, hD, hE, hF, quarticEq_CA_of_raw hEqRaw_CA, hEqRaw_DA, quarticEq_EA_of_raw hEqRaw_EA, hEqRaw_FA, hRaw_BA, quarticCmp_GA_of_raw hRaw_GA⟩
            · -- ACDE strictly outranks F
              have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
              have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks ACDE
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_eq_lt_CAG hEqRaw_CA hRaw_AG
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_eq_lt_DAG hEqRaw_DA hRaw_AG
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_eq_lt_EAG hEqRaw_EA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FAG hRaw_FA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties ACDE
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneACDEG ?_
                  refine ⟨hA, hC, hD, hE, hG, quarticEq_CA_of_raw hEqRaw_CA, hEqRaw_DA, quarticEq_EA_of_raw hEqRaw_EA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, hRaw_FA⟩
                · -- ACDE strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneACDE ?_
                  refine ⟨hA, hC, hD, hE, quarticEq_CA_of_raw hEqRaw_CA, hEqRaw_DA, quarticEq_EA_of_raw hEqRaw_EA, hRaw_BA, hRaw_FA, quarticCmp_GA_of_raw hRaw_GA⟩
        · -- ACD strictly outranks E
          have hRed_EA : E.natDegree < 3 * A.natDegree := quarticScore_not_lt_not_eq hAElt hAEeq
          have hRaw_EA : 2 * E.natDegree < 6 * A.natDegree := quarticCmp_EA_to_raw hRed_EA
          by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
          · -- F strictly outranks ACD
            have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
            have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_eq_lt_CAF hEqRaw_CA hRaw_AF
            have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_eq_lt_DAF hEqRaw_DA hRaw_AF
            have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BAF hRaw_BA hRaw_AF
            have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_lt_trans_EAF hRaw_EA hRaw_AF
            by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
            · -- G strictly outranks F
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
              · -- G ties F
                have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
                refine QuarticSupportCone810.coneFG ?_
                refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
              · -- F strictly outranks G
                have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
                have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
                refine QuarticSupportCone810.coneF ?_
                refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
          · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
            · -- F ties ACD
              have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks ACDF
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_eq_lt_CAG hEqRaw_CA hRaw_AG
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_eq_lt_DAG hEqRaw_DA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FAG hEqRaw_FA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EAG hRaw_EA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties ACDF
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneACDFG ?_
                  refine ⟨hA, hC, hD, hF, hG, quarticEq_CA_of_raw hEqRaw_CA, hEqRaw_DA, hEqRaw_FA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, quarticCmp_EA_of_raw hRaw_EA⟩
                · -- ACDF strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneACDF ?_
                  refine ⟨hA, hC, hD, hF, quarticEq_CA_of_raw hEqRaw_CA, hEqRaw_DA, hEqRaw_FA, hRaw_BA, quarticCmp_EA_of_raw hRaw_EA, quarticCmp_GA_of_raw hRaw_GA⟩
            · -- ACD strictly outranks F
              have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
              have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks ACD
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_eq_lt_CAG hEqRaw_CA hRaw_AG
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_eq_lt_DAG hEqRaw_DA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EAG hRaw_EA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FAG hRaw_FA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties ACD
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneACDG ?_
                  refine ⟨hA, hC, hD, hG, quarticEq_CA_of_raw hEqRaw_CA, hEqRaw_DA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, quarticCmp_EA_of_raw hRaw_EA, hRaw_FA⟩
                · -- ACD strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneACD ?_
                  refine ⟨hA, hC, hD, quarticEq_CA_of_raw hEqRaw_CA, hEqRaw_DA, hRaw_BA, quarticCmp_EA_of_raw hRaw_EA, hRaw_FA, quarticCmp_GA_of_raw hRaw_GA⟩
    · -- AC strictly outranks D
      have hRed_DA : 2 * D.natDegree < 5 * A.natDegree := quarticScore_not_lt_not_eq hADlt hADeq
      have hRaw_DA : 2 * D.natDegree < 5 * A.natDegree := hRed_DA
      by_cases hAElt : 3 * A.natDegree < E.natDegree
      · -- E strictly outranks AC
        have hRaw_AE : 6 * A.natDegree < 2 * E.natDegree := quarticCmp_AE_to_raw hAElt
        have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticScore_eq_lt_CAE hEqRaw_CA hRaw_AE
        have hRaw_BE : 6 * B.natDegree < 3 * E.natDegree := quarticScore_lt_trans_BAE hRaw_BA hRaw_AE
        have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := quarticScore_lt_trans_DAE hRaw_DA hRaw_AE
        by_cases hEFlt : 7 * E.natDegree < 6 * F.natDegree
        · -- F strictly outranks E
          have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := hEFlt
          have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := quarticScore_lt_trans_AEF hRaw_AE hRaw_EF
          have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BEF hRaw_BE hRaw_EF
          have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CEF hRaw_CE hRaw_EF
          have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_lt_trans_DEF hRaw_DE hRaw_EF
          by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
          · -- G strictly outranks F
            have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
            have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
            have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
            have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
            have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
            have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
            refine QuarticSupportCone810.coneG ?_
            refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
          · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
            · -- G ties F
              have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
              refine QuarticSupportCone810.coneFG ?_
              refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
            · -- F strictly outranks G
              have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
              have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
              refine QuarticSupportCone810.coneF ?_
              refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
        · by_cases hEFeq : 7 * E.natDegree = 6 * F.natDegree
          · -- F ties E
            have hEqRaw_FE : 6 * F.natDegree = 7 * E.natDegree := hEFeq.symm
            by_cases hEGlt : 4 * E.natDegree < 3 * G.natDegree
            · -- G strictly outranks EF
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticCmp_EG_to_raw hEGlt
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FEG hEqRaw_FE hRaw_EG
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AEG hRaw_AE hRaw_EG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BEG hRaw_BE hRaw_EG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CEG hRaw_CE hRaw_EG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DEG hRaw_DE hRaw_EG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hEGeq : 4 * E.natDegree = 3 * G.natDegree
              · -- G ties EF
                have hEqRaw_GE : 6 * G.natDegree = 8 * E.natDegree := quarticEq_GE_to_raw (hEGeq.symm)
                refine QuarticSupportCone810.coneEFG ?_
                refine ⟨hE, hF, hG, hEqRaw_FE, quarticEq_GE_of_raw hEqRaw_GE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE⟩
              · -- EF strictly outranks G
                have hRed_GE : 3 * G.natDegree < 4 * E.natDegree := quarticScore_not_lt_not_eq hEGlt hEGeq
                have hRaw_GE : 6 * G.natDegree < 8 * E.natDegree := quarticCmp_GE_to_raw hRed_GE
                refine QuarticSupportCone810.coneEF ?_
                refine ⟨hE, hF, hEqRaw_FE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, quarticCmp_GE_of_raw hRaw_GE⟩
          · -- E strictly outranks F
            have hRed_FE : 6 * F.natDegree < 7 * E.natDegree := quarticScore_not_lt_not_eq hEFlt hEFeq
            have hRaw_FE : 6 * F.natDegree < 7 * E.natDegree := hRed_FE
            by_cases hEGlt : 4 * E.natDegree < 3 * G.natDegree
            · -- G strictly outranks E
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticCmp_EG_to_raw hEGlt
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AEG hRaw_AE hRaw_EG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BEG hRaw_BE hRaw_EG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CEG hRaw_CE hRaw_EG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DEG hRaw_DE hRaw_EG
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FEG hRaw_FE hRaw_EG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hEGeq : 4 * E.natDegree = 3 * G.natDegree
              · -- G ties E
                have hEqRaw_GE : 6 * G.natDegree = 8 * E.natDegree := quarticEq_GE_to_raw (hEGeq.symm)
                refine QuarticSupportCone810.coneEG ?_
                refine ⟨hE, hG, quarticEq_GE_of_raw hEqRaw_GE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, hRaw_FE⟩
              · -- E strictly outranks G
                have hRed_GE : 3 * G.natDegree < 4 * E.natDegree := quarticScore_not_lt_not_eq hEGlt hEGeq
                have hRaw_GE : 6 * G.natDegree < 8 * E.natDegree := quarticCmp_GE_to_raw hRed_GE
                refine QuarticSupportCone810.coneE ?_
                refine ⟨hE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, hRaw_FE, quarticCmp_GE_of_raw hRaw_GE⟩
      · by_cases hAEeq : 3 * A.natDegree = E.natDegree
        · -- E ties AC
          have hEqRaw_EA : 2 * E.natDegree = 6 * A.natDegree := quarticEq_EA_to_raw (hAEeq.symm)
          by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
          · -- F strictly outranks ACE
            have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
            have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_eq_lt_CAF hEqRaw_CA hRaw_AF
            have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_eq_lt_EAF hEqRaw_EA hRaw_AF
            have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BAF hRaw_BA hRaw_AF
            have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_lt_trans_DAF hRaw_DA hRaw_AF
            by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
            · -- G strictly outranks F
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
              · -- G ties F
                have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
                refine QuarticSupportCone810.coneFG ?_
                refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
              · -- F strictly outranks G
                have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
                have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
                refine QuarticSupportCone810.coneF ?_
                refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
          · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
            · -- F ties ACE
              have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks ACEF
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_eq_lt_CAG hEqRaw_CA hRaw_AG
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_eq_lt_EAG hEqRaw_EA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FAG hEqRaw_FA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DAG hRaw_DA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties ACEF
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneACEFG ?_
                  refine ⟨hA, hC, hE, hF, hG, quarticEq_CA_of_raw hEqRaw_CA, quarticEq_EA_of_raw hEqRaw_EA, hEqRaw_FA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, hRaw_DA⟩
                · -- ACEF strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneACEF ?_
                  refine ⟨hA, hC, hE, hF, quarticEq_CA_of_raw hEqRaw_CA, quarticEq_EA_of_raw hEqRaw_EA, hEqRaw_FA, hRaw_BA, hRaw_DA, quarticCmp_GA_of_raw hRaw_GA⟩
            · -- ACE strictly outranks F
              have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
              have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks ACE
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_eq_lt_CAG hEqRaw_CA hRaw_AG
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_eq_lt_EAG hEqRaw_EA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DAG hRaw_DA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FAG hRaw_FA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties ACE
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneACEG ?_
                  refine ⟨hA, hC, hE, hG, quarticEq_CA_of_raw hEqRaw_CA, quarticEq_EA_of_raw hEqRaw_EA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, hRaw_DA, hRaw_FA⟩
                · -- ACE strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneACE ?_
                  refine ⟨hA, hC, hE, quarticEq_CA_of_raw hEqRaw_CA, quarticEq_EA_of_raw hEqRaw_EA, hRaw_BA, hRaw_DA, hRaw_FA, quarticCmp_GA_of_raw hRaw_GA⟩
        · -- AC strictly outranks E
          have hRed_EA : E.natDegree < 3 * A.natDegree := quarticScore_not_lt_not_eq hAElt hAEeq
          have hRaw_EA : 2 * E.natDegree < 6 * A.natDegree := quarticCmp_EA_to_raw hRed_EA
          by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
          · -- F strictly outranks AC
            have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
            have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_eq_lt_CAF hEqRaw_CA hRaw_AF
            have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BAF hRaw_BA hRaw_AF
            have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_lt_trans_DAF hRaw_DA hRaw_AF
            have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_lt_trans_EAF hRaw_EA hRaw_AF
            by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
            · -- G strictly outranks F
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
              · -- G ties F
                have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
                refine QuarticSupportCone810.coneFG ?_
                refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
              · -- F strictly outranks G
                have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
                have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
                refine QuarticSupportCone810.coneF ?_
                refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
          · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
            · -- F ties AC
              have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks ACF
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_eq_lt_CAG hEqRaw_CA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FAG hEqRaw_FA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DAG hRaw_DA hRaw_AG
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EAG hRaw_EA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties ACF
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneACFG ?_
                  refine ⟨hA, hC, hF, hG, quarticEq_CA_of_raw hEqRaw_CA, hEqRaw_FA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, hRaw_DA, quarticCmp_EA_of_raw hRaw_EA⟩
                · -- ACF strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneACF ?_
                  refine ⟨hA, hC, hF, quarticEq_CA_of_raw hEqRaw_CA, hEqRaw_FA, hRaw_BA, hRaw_DA, quarticCmp_EA_of_raw hRaw_EA, quarticCmp_GA_of_raw hRaw_GA⟩
            · -- AC strictly outranks F
              have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
              have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks AC
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_eq_lt_CAG hEqRaw_CA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DAG hRaw_DA hRaw_AG
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EAG hRaw_EA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FAG hRaw_FA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties AC
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneACG ?_
                  refine ⟨hA, hC, hG, quarticEq_CA_of_raw hEqRaw_CA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, hRaw_DA, quarticCmp_EA_of_raw hRaw_EA, hRaw_FA⟩
                · -- AC strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneAC ?_
                  refine ⟨hA, hC, quarticEq_CA_of_raw hEqRaw_CA, hRaw_BA, hRaw_DA, quarticCmp_EA_of_raw hRaw_EA, hRaw_FA, quarticCmp_GA_of_raw hRaw_GA⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_ABCDEFG_cand_A_rest_DEFG
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB : 0 < B.natDegree)
    (hC : 0 < C.natDegree)
    (hD : 0 < D.natDegree)
    (hE : 0 < E.natDegree)
    (hF : 0 < F.natDegree)
    (hG : 0 < G.natDegree)
    (hRaw_BA : 2 * B.natDegree < 3 * A.natDegree)
    (hRaw_CA : 2 * C.natDegree < 4 * A.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
  · -- D strictly outranks A
    have hRaw_AD : 5 * A.natDegree < 2 * D.natDegree := hADlt
    have hRaw_BD : 5 * B.natDegree < 3 * D.natDegree := quarticScore_lt_trans_BAD hRaw_BA hRaw_AD
    have hRaw_CD : 5 * C.natDegree < 4 * D.natDegree := quarticScore_lt_trans_CAD hRaw_CA hRaw_AD
    by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
    · -- E strictly outranks D
      have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := hDElt
      have hRaw_AE : 6 * A.natDegree < 2 * E.natDegree := quarticScore_lt_trans_ADE hRaw_AD hRaw_DE
      have hRaw_BE : 6 * B.natDegree < 3 * E.natDegree := quarticScore_lt_trans_BDE hRaw_BD hRaw_DE
      have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticScore_lt_trans_CDE hRaw_CD hRaw_DE
      by_cases hEFlt : 7 * E.natDegree < 6 * F.natDegree
      · -- F strictly outranks E
        have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := hEFlt
        have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := quarticScore_lt_trans_AEF hRaw_AE hRaw_EF
        have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BEF hRaw_BE hRaw_EF
        have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CEF hRaw_CE hRaw_EF
        have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_lt_trans_DEF hRaw_DE hRaw_EF
        by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
        · -- G strictly outranks F
          have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
          have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
          have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
          have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
          have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
          have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
          refine QuarticSupportCone810.coneG ?_
          refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
        · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
          · -- G ties F
            have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
            refine QuarticSupportCone810.coneFG ?_
            refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
          · -- F strictly outranks G
            have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
            have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
            refine QuarticSupportCone810.coneF ?_
            refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
      · by_cases hEFeq : 7 * E.natDegree = 6 * F.natDegree
        · -- F ties E
          have hEqRaw_FE : 6 * F.natDegree = 7 * E.natDegree := hEFeq.symm
          by_cases hEGlt : 4 * E.natDegree < 3 * G.natDegree
          · -- G strictly outranks EF
            have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticCmp_EG_to_raw hEGlt
            have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FEG hEqRaw_FE hRaw_EG
            have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AEG hRaw_AE hRaw_EG
            have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BEG hRaw_BE hRaw_EG
            have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CEG hRaw_CE hRaw_EG
            have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DEG hRaw_DE hRaw_EG
            refine QuarticSupportCone810.coneG ?_
            refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
          · by_cases hEGeq : 4 * E.natDegree = 3 * G.natDegree
            · -- G ties EF
              have hEqRaw_GE : 6 * G.natDegree = 8 * E.natDegree := quarticEq_GE_to_raw (hEGeq.symm)
              refine QuarticSupportCone810.coneEFG ?_
              refine ⟨hE, hF, hG, hEqRaw_FE, quarticEq_GE_of_raw hEqRaw_GE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE⟩
            · -- EF strictly outranks G
              have hRed_GE : 3 * G.natDegree < 4 * E.natDegree := quarticScore_not_lt_not_eq hEGlt hEGeq
              have hRaw_GE : 6 * G.natDegree < 8 * E.natDegree := quarticCmp_GE_to_raw hRed_GE
              refine QuarticSupportCone810.coneEF ?_
              refine ⟨hE, hF, hEqRaw_FE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, quarticCmp_GE_of_raw hRaw_GE⟩
        · -- E strictly outranks F
          have hRed_FE : 6 * F.natDegree < 7 * E.natDegree := quarticScore_not_lt_not_eq hEFlt hEFeq
          have hRaw_FE : 6 * F.natDegree < 7 * E.natDegree := hRed_FE
          by_cases hEGlt : 4 * E.natDegree < 3 * G.natDegree
          · -- G strictly outranks E
            have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticCmp_EG_to_raw hEGlt
            have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AEG hRaw_AE hRaw_EG
            have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BEG hRaw_BE hRaw_EG
            have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CEG hRaw_CE hRaw_EG
            have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DEG hRaw_DE hRaw_EG
            have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FEG hRaw_FE hRaw_EG
            refine QuarticSupportCone810.coneG ?_
            refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
          · by_cases hEGeq : 4 * E.natDegree = 3 * G.natDegree
            · -- G ties E
              have hEqRaw_GE : 6 * G.natDegree = 8 * E.natDegree := quarticEq_GE_to_raw (hEGeq.symm)
              refine QuarticSupportCone810.coneEG ?_
              refine ⟨hE, hG, quarticEq_GE_of_raw hEqRaw_GE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, hRaw_FE⟩
            · -- E strictly outranks G
              have hRed_GE : 3 * G.natDegree < 4 * E.natDegree := quarticScore_not_lt_not_eq hEGlt hEGeq
              have hRaw_GE : 6 * G.natDegree < 8 * E.natDegree := quarticCmp_GE_to_raw hRed_GE
              refine QuarticSupportCone810.coneE ?_
              refine ⟨hE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, hRaw_FE, quarticCmp_GE_of_raw hRaw_GE⟩
    · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
      · -- E ties D
        have hEqRaw_ED : 5 * E.natDegree = 6 * D.natDegree := hDEeq.symm
        by_cases hDFlt : 7 * D.natDegree < 5 * F.natDegree
        · -- F strictly outranks DE
          have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := hDFlt
          have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_eq_lt_EDF hEqRaw_ED hRaw_DF
          have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := quarticScore_lt_trans_ADF hRaw_AD hRaw_DF
          have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BDF hRaw_BD hRaw_DF
          have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CDF hRaw_CD hRaw_DF
          by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
          · -- G strictly outranks F
            have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
            have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
            have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
            have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
            have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
            have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
            refine QuarticSupportCone810.coneG ?_
            refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
          · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
            · -- G ties F
              have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
              refine QuarticSupportCone810.coneFG ?_
              refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
            · -- F strictly outranks G
              have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
              have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
              refine QuarticSupportCone810.coneF ?_
              refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
        · by_cases hDFeq : 7 * D.natDegree = 5 * F.natDegree
          · -- F ties DE
            have hEqRaw_FD : 5 * F.natDegree = 7 * D.natDegree := hDFeq.symm
            by_cases hDGlt : 8 * D.natDegree < 5 * G.natDegree
            · -- G strictly outranks DEF
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := hDGlt
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_eq_lt_EDG hEqRaw_ED hRaw_DG
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FDG hEqRaw_FD hRaw_DG
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_ADG hRaw_AD hRaw_DG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BDG hRaw_BD hRaw_DG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CDG hRaw_CD hRaw_DG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hDGeq : 8 * D.natDegree = 5 * G.natDegree
              · -- G ties DEF
                have hEqRaw_GD : 5 * G.natDegree = 8 * D.natDegree := hDGeq.symm
                refine QuarticSupportCone810.coneDEFG ?_
                refine ⟨hD, hE, hF, hG, hEqRaw_ED, hEqRaw_FD, hEqRaw_GD, hRaw_AD, hRaw_BD, hRaw_CD⟩
              · -- DEF strictly outranks G
                have hRed_GD : 5 * G.natDegree < 8 * D.natDegree := quarticScore_not_lt_not_eq hDGlt hDGeq
                have hRaw_GD : 5 * G.natDegree < 8 * D.natDegree := hRed_GD
                refine QuarticSupportCone810.coneDEF ?_
                refine ⟨hD, hE, hF, hEqRaw_ED, hEqRaw_FD, hRaw_AD, hRaw_BD, hRaw_CD, hRaw_GD⟩
          · -- DE strictly outranks F
            have hRed_FD : 5 * F.natDegree < 7 * D.natDegree := quarticScore_not_lt_not_eq hDFlt hDFeq
            have hRaw_FD : 5 * F.natDegree < 7 * D.natDegree := hRed_FD
            by_cases hDGlt : 8 * D.natDegree < 5 * G.natDegree
            · -- G strictly outranks DE
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := hDGlt
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_eq_lt_EDG hEqRaw_ED hRaw_DG
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_ADG hRaw_AD hRaw_DG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BDG hRaw_BD hRaw_DG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CDG hRaw_CD hRaw_DG
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FDG hRaw_FD hRaw_DG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hDGeq : 8 * D.natDegree = 5 * G.natDegree
              · -- G ties DE
                have hEqRaw_GD : 5 * G.natDegree = 8 * D.natDegree := hDGeq.symm
                refine QuarticSupportCone810.coneDEG ?_
                refine ⟨hD, hE, hG, hEqRaw_ED, hEqRaw_GD, hRaw_AD, hRaw_BD, hRaw_CD, hRaw_FD⟩
              · -- DE strictly outranks G
                have hRed_GD : 5 * G.natDegree < 8 * D.natDegree := quarticScore_not_lt_not_eq hDGlt hDGeq
                have hRaw_GD : 5 * G.natDegree < 8 * D.natDegree := hRed_GD
                refine QuarticSupportCone810.coneDE ?_
                refine ⟨hD, hE, hEqRaw_ED, hRaw_AD, hRaw_BD, hRaw_CD, hRaw_FD, hRaw_GD⟩
      · -- D strictly outranks E
        have hRed_ED : 5 * E.natDegree < 6 * D.natDegree := quarticScore_not_lt_not_eq hDElt hDEeq
        have hRaw_ED : 5 * E.natDegree < 6 * D.natDegree := hRed_ED
        by_cases hDFlt : 7 * D.natDegree < 5 * F.natDegree
        · -- F strictly outranks D
          have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := hDFlt
          have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := quarticScore_lt_trans_ADF hRaw_AD hRaw_DF
          have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BDF hRaw_BD hRaw_DF
          have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CDF hRaw_CD hRaw_DF
          have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_lt_trans_EDF hRaw_ED hRaw_DF
          by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
          · -- G strictly outranks F
            have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
            have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
            have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
            have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
            have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
            have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
            refine QuarticSupportCone810.coneG ?_
            refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
          · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
            · -- G ties F
              have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
              refine QuarticSupportCone810.coneFG ?_
              refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
            · -- F strictly outranks G
              have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
              have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
              refine QuarticSupportCone810.coneF ?_
              refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
        · by_cases hDFeq : 7 * D.natDegree = 5 * F.natDegree
          · -- F ties D
            have hEqRaw_FD : 5 * F.natDegree = 7 * D.natDegree := hDFeq.symm
            by_cases hDGlt : 8 * D.natDegree < 5 * G.natDegree
            · -- G strictly outranks DF
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := hDGlt
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FDG hEqRaw_FD hRaw_DG
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_ADG hRaw_AD hRaw_DG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BDG hRaw_BD hRaw_DG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CDG hRaw_CD hRaw_DG
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EDG hRaw_ED hRaw_DG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hDGeq : 8 * D.natDegree = 5 * G.natDegree
              · -- G ties DF
                have hEqRaw_GD : 5 * G.natDegree = 8 * D.natDegree := hDGeq.symm
                refine QuarticSupportCone810.coneDFG ?_
                refine ⟨hD, hF, hG, hEqRaw_FD, hEqRaw_GD, hRaw_AD, hRaw_BD, hRaw_CD, hRaw_ED⟩
              · -- DF strictly outranks G
                have hRed_GD : 5 * G.natDegree < 8 * D.natDegree := quarticScore_not_lt_not_eq hDGlt hDGeq
                have hRaw_GD : 5 * G.natDegree < 8 * D.natDegree := hRed_GD
                refine QuarticSupportCone810.coneDF ?_
                refine ⟨hD, hF, hEqRaw_FD, hRaw_AD, hRaw_BD, hRaw_CD, hRaw_ED, hRaw_GD⟩
          · -- D strictly outranks F
            have hRed_FD : 5 * F.natDegree < 7 * D.natDegree := quarticScore_not_lt_not_eq hDFlt hDFeq
            have hRaw_FD : 5 * F.natDegree < 7 * D.natDegree := hRed_FD
            by_cases hDGlt : 8 * D.natDegree < 5 * G.natDegree
            · -- G strictly outranks D
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := hDGlt
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_ADG hRaw_AD hRaw_DG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BDG hRaw_BD hRaw_DG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CDG hRaw_CD hRaw_DG
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EDG hRaw_ED hRaw_DG
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FDG hRaw_FD hRaw_DG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hDGeq : 8 * D.natDegree = 5 * G.natDegree
              · -- G ties D
                have hEqRaw_GD : 5 * G.natDegree = 8 * D.natDegree := hDGeq.symm
                refine QuarticSupportCone810.coneDG ?_
                refine ⟨hD, hG, hEqRaw_GD, hRaw_AD, hRaw_BD, hRaw_CD, hRaw_ED, hRaw_FD⟩
              · -- D strictly outranks G
                have hRed_GD : 5 * G.natDegree < 8 * D.natDegree := quarticScore_not_lt_not_eq hDGlt hDGeq
                have hRaw_GD : 5 * G.natDegree < 8 * D.natDegree := hRed_GD
                refine QuarticSupportCone810.coneD ?_
                refine ⟨hD, hRaw_AD, hRaw_BD, hRaw_CD, hRaw_ED, hRaw_FD, hRaw_GD⟩
  · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
    · -- D ties A
      have hEqRaw_DA : 2 * D.natDegree = 5 * A.natDegree := hADeq.symm
      by_cases hAElt : 3 * A.natDegree < E.natDegree
      · -- E strictly outranks AD
        have hRaw_AE : 6 * A.natDegree < 2 * E.natDegree := quarticCmp_AE_to_raw hAElt
        have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := quarticScore_eq_lt_DAE hEqRaw_DA hRaw_AE
        have hRaw_BE : 6 * B.natDegree < 3 * E.natDegree := quarticScore_lt_trans_BAE hRaw_BA hRaw_AE
        have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticScore_lt_trans_CAE hRaw_CA hRaw_AE
        by_cases hEFlt : 7 * E.natDegree < 6 * F.natDegree
        · -- F strictly outranks E
          have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := hEFlt
          have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := quarticScore_lt_trans_AEF hRaw_AE hRaw_EF
          have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BEF hRaw_BE hRaw_EF
          have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CEF hRaw_CE hRaw_EF
          have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_lt_trans_DEF hRaw_DE hRaw_EF
          by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
          · -- G strictly outranks F
            have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
            have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
            have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
            have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
            have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
            have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
            refine QuarticSupportCone810.coneG ?_
            refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
          · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
            · -- G ties F
              have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
              refine QuarticSupportCone810.coneFG ?_
              refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
            · -- F strictly outranks G
              have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
              have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
              refine QuarticSupportCone810.coneF ?_
              refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
        · by_cases hEFeq : 7 * E.natDegree = 6 * F.natDegree
          · -- F ties E
            have hEqRaw_FE : 6 * F.natDegree = 7 * E.natDegree := hEFeq.symm
            by_cases hEGlt : 4 * E.natDegree < 3 * G.natDegree
            · -- G strictly outranks EF
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticCmp_EG_to_raw hEGlt
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FEG hEqRaw_FE hRaw_EG
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AEG hRaw_AE hRaw_EG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BEG hRaw_BE hRaw_EG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CEG hRaw_CE hRaw_EG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DEG hRaw_DE hRaw_EG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hEGeq : 4 * E.natDegree = 3 * G.natDegree
              · -- G ties EF
                have hEqRaw_GE : 6 * G.natDegree = 8 * E.natDegree := quarticEq_GE_to_raw (hEGeq.symm)
                refine QuarticSupportCone810.coneEFG ?_
                refine ⟨hE, hF, hG, hEqRaw_FE, quarticEq_GE_of_raw hEqRaw_GE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE⟩
              · -- EF strictly outranks G
                have hRed_GE : 3 * G.natDegree < 4 * E.natDegree := quarticScore_not_lt_not_eq hEGlt hEGeq
                have hRaw_GE : 6 * G.natDegree < 8 * E.natDegree := quarticCmp_GE_to_raw hRed_GE
                refine QuarticSupportCone810.coneEF ?_
                refine ⟨hE, hF, hEqRaw_FE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, quarticCmp_GE_of_raw hRaw_GE⟩
          · -- E strictly outranks F
            have hRed_FE : 6 * F.natDegree < 7 * E.natDegree := quarticScore_not_lt_not_eq hEFlt hEFeq
            have hRaw_FE : 6 * F.natDegree < 7 * E.natDegree := hRed_FE
            by_cases hEGlt : 4 * E.natDegree < 3 * G.natDegree
            · -- G strictly outranks E
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticCmp_EG_to_raw hEGlt
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AEG hRaw_AE hRaw_EG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BEG hRaw_BE hRaw_EG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CEG hRaw_CE hRaw_EG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DEG hRaw_DE hRaw_EG
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FEG hRaw_FE hRaw_EG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hEGeq : 4 * E.natDegree = 3 * G.natDegree
              · -- G ties E
                have hEqRaw_GE : 6 * G.natDegree = 8 * E.natDegree := quarticEq_GE_to_raw (hEGeq.symm)
                refine QuarticSupportCone810.coneEG ?_
                refine ⟨hE, hG, quarticEq_GE_of_raw hEqRaw_GE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, hRaw_FE⟩
              · -- E strictly outranks G
                have hRed_GE : 3 * G.natDegree < 4 * E.natDegree := quarticScore_not_lt_not_eq hEGlt hEGeq
                have hRaw_GE : 6 * G.natDegree < 8 * E.natDegree := quarticCmp_GE_to_raw hRed_GE
                refine QuarticSupportCone810.coneE ?_
                refine ⟨hE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, hRaw_FE, quarticCmp_GE_of_raw hRaw_GE⟩
      · by_cases hAEeq : 3 * A.natDegree = E.natDegree
        · -- E ties AD
          have hEqRaw_EA : 2 * E.natDegree = 6 * A.natDegree := quarticEq_EA_to_raw (hAEeq.symm)
          by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
          · -- F strictly outranks ADE
            have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
            have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_eq_lt_DAF hEqRaw_DA hRaw_AF
            have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_eq_lt_EAF hEqRaw_EA hRaw_AF
            have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BAF hRaw_BA hRaw_AF
            have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CAF hRaw_CA hRaw_AF
            by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
            · -- G strictly outranks F
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
              · -- G ties F
                have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
                refine QuarticSupportCone810.coneFG ?_
                refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
              · -- F strictly outranks G
                have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
                have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
                refine QuarticSupportCone810.coneF ?_
                refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
          · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
            · -- F ties ADE
              have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks ADEF
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_eq_lt_DAG hEqRaw_DA hRaw_AG
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_eq_lt_EAG hEqRaw_EA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FAG hEqRaw_FA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CAG hRaw_CA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties ADEF
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneADEFG ?_
                  refine ⟨hA, hD, hE, hF, hG, hEqRaw_DA, quarticEq_EA_of_raw hEqRaw_EA, hEqRaw_FA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA⟩
                · -- ADEF strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneADEF ?_
                  refine ⟨hA, hD, hE, hF, hEqRaw_DA, quarticEq_EA_of_raw hEqRaw_EA, hEqRaw_FA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, quarticCmp_GA_of_raw hRaw_GA⟩
            · -- ADE strictly outranks F
              have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
              have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks ADE
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_eq_lt_DAG hEqRaw_DA hRaw_AG
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_eq_lt_EAG hEqRaw_EA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CAG hRaw_CA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FAG hRaw_FA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties ADE
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneADEG ?_
                  refine ⟨hA, hD, hE, hG, hEqRaw_DA, quarticEq_EA_of_raw hEqRaw_EA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, hRaw_FA⟩
                · -- ADE strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneADE ?_
                  refine ⟨hA, hD, hE, hEqRaw_DA, quarticEq_EA_of_raw hEqRaw_EA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, hRaw_FA, quarticCmp_GA_of_raw hRaw_GA⟩
        · -- AD strictly outranks E
          have hRed_EA : E.natDegree < 3 * A.natDegree := quarticScore_not_lt_not_eq hAElt hAEeq
          have hRaw_EA : 2 * E.natDegree < 6 * A.natDegree := quarticCmp_EA_to_raw hRed_EA
          by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
          · -- F strictly outranks AD
            have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
            have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_eq_lt_DAF hEqRaw_DA hRaw_AF
            have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BAF hRaw_BA hRaw_AF
            have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CAF hRaw_CA hRaw_AF
            have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_lt_trans_EAF hRaw_EA hRaw_AF
            by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
            · -- G strictly outranks F
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
              · -- G ties F
                have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
                refine QuarticSupportCone810.coneFG ?_
                refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
              · -- F strictly outranks G
                have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
                have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
                refine QuarticSupportCone810.coneF ?_
                refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
          · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
            · -- F ties AD
              have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks ADF
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_eq_lt_DAG hEqRaw_DA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FAG hEqRaw_FA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CAG hRaw_CA hRaw_AG
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EAG hRaw_EA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties ADF
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneADFG ?_
                  refine ⟨hA, hD, hF, hG, hEqRaw_DA, hEqRaw_FA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, quarticCmp_EA_of_raw hRaw_EA⟩
                · -- ADF strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneADF ?_
                  refine ⟨hA, hD, hF, hEqRaw_DA, hEqRaw_FA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, quarticCmp_EA_of_raw hRaw_EA, quarticCmp_GA_of_raw hRaw_GA⟩
            · -- AD strictly outranks F
              have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
              have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks AD
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_eq_lt_DAG hEqRaw_DA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CAG hRaw_CA hRaw_AG
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EAG hRaw_EA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FAG hRaw_FA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties AD
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneADG ?_
                  refine ⟨hA, hD, hG, hEqRaw_DA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, quarticCmp_EA_of_raw hRaw_EA, hRaw_FA⟩
                · -- AD strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneAD ?_
                  refine ⟨hA, hD, hEqRaw_DA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, quarticCmp_EA_of_raw hRaw_EA, hRaw_FA, quarticCmp_GA_of_raw hRaw_GA⟩
    · -- A strictly outranks D
      have hRed_DA : 2 * D.natDegree < 5 * A.natDegree := quarticScore_not_lt_not_eq hADlt hADeq
      have hRaw_DA : 2 * D.natDegree < 5 * A.natDegree := hRed_DA
      by_cases hAElt : 3 * A.natDegree < E.natDegree
      · -- E strictly outranks A
        have hRaw_AE : 6 * A.natDegree < 2 * E.natDegree := quarticCmp_AE_to_raw hAElt
        have hRaw_BE : 6 * B.natDegree < 3 * E.natDegree := quarticScore_lt_trans_BAE hRaw_BA hRaw_AE
        have hRaw_CE : 6 * C.natDegree < 4 * E.natDegree := quarticScore_lt_trans_CAE hRaw_CA hRaw_AE
        have hRaw_DE : 6 * D.natDegree < 5 * E.natDegree := quarticScore_lt_trans_DAE hRaw_DA hRaw_AE
        by_cases hEFlt : 7 * E.natDegree < 6 * F.natDegree
        · -- F strictly outranks E
          have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := hEFlt
          have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := quarticScore_lt_trans_AEF hRaw_AE hRaw_EF
          have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BEF hRaw_BE hRaw_EF
          have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CEF hRaw_CE hRaw_EF
          have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_lt_trans_DEF hRaw_DE hRaw_EF
          by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
          · -- G strictly outranks F
            have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
            have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
            have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
            have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
            have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
            have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
            refine QuarticSupportCone810.coneG ?_
            refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
          · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
            · -- G ties F
              have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
              refine QuarticSupportCone810.coneFG ?_
              refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
            · -- F strictly outranks G
              have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
              have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
              refine QuarticSupportCone810.coneF ?_
              refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
        · by_cases hEFeq : 7 * E.natDegree = 6 * F.natDegree
          · -- F ties E
            have hEqRaw_FE : 6 * F.natDegree = 7 * E.natDegree := hEFeq.symm
            by_cases hEGlt : 4 * E.natDegree < 3 * G.natDegree
            · -- G strictly outranks EF
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticCmp_EG_to_raw hEGlt
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FEG hEqRaw_FE hRaw_EG
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AEG hRaw_AE hRaw_EG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BEG hRaw_BE hRaw_EG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CEG hRaw_CE hRaw_EG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DEG hRaw_DE hRaw_EG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hEGeq : 4 * E.natDegree = 3 * G.natDegree
              · -- G ties EF
                have hEqRaw_GE : 6 * G.natDegree = 8 * E.natDegree := quarticEq_GE_to_raw (hEGeq.symm)
                refine QuarticSupportCone810.coneEFG ?_
                refine ⟨hE, hF, hG, hEqRaw_FE, quarticEq_GE_of_raw hEqRaw_GE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE⟩
              · -- EF strictly outranks G
                have hRed_GE : 3 * G.natDegree < 4 * E.natDegree := quarticScore_not_lt_not_eq hEGlt hEGeq
                have hRaw_GE : 6 * G.natDegree < 8 * E.natDegree := quarticCmp_GE_to_raw hRed_GE
                refine QuarticSupportCone810.coneEF ?_
                refine ⟨hE, hF, hEqRaw_FE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, quarticCmp_GE_of_raw hRaw_GE⟩
          · -- E strictly outranks F
            have hRed_FE : 6 * F.natDegree < 7 * E.natDegree := quarticScore_not_lt_not_eq hEFlt hEFeq
            have hRaw_FE : 6 * F.natDegree < 7 * E.natDegree := hRed_FE
            by_cases hEGlt : 4 * E.natDegree < 3 * G.natDegree
            · -- G strictly outranks E
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticCmp_EG_to_raw hEGlt
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AEG hRaw_AE hRaw_EG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BEG hRaw_BE hRaw_EG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CEG hRaw_CE hRaw_EG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DEG hRaw_DE hRaw_EG
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FEG hRaw_FE hRaw_EG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hEGeq : 4 * E.natDegree = 3 * G.natDegree
              · -- G ties E
                have hEqRaw_GE : 6 * G.natDegree = 8 * E.natDegree := quarticEq_GE_to_raw (hEGeq.symm)
                refine QuarticSupportCone810.coneEG ?_
                refine ⟨hE, hG, quarticEq_GE_of_raw hEqRaw_GE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, hRaw_FE⟩
              · -- E strictly outranks G
                have hRed_GE : 3 * G.natDegree < 4 * E.natDegree := quarticScore_not_lt_not_eq hEGlt hEGeq
                have hRaw_GE : 6 * G.natDegree < 8 * E.natDegree := quarticCmp_GE_to_raw hRed_GE
                refine QuarticSupportCone810.coneE ?_
                refine ⟨hE, quarticCmp_AE_of_raw hRaw_AE, quarticCmp_BE_of_raw hRaw_BE, quarticCmp_CE_of_raw hRaw_CE, hRaw_DE, hRaw_FE, quarticCmp_GE_of_raw hRaw_GE⟩
      · by_cases hAEeq : 3 * A.natDegree = E.natDegree
        · -- E ties A
          have hEqRaw_EA : 2 * E.natDegree = 6 * A.natDegree := quarticEq_EA_to_raw (hAEeq.symm)
          by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
          · -- F strictly outranks AE
            have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
            have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_eq_lt_EAF hEqRaw_EA hRaw_AF
            have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BAF hRaw_BA hRaw_AF
            have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CAF hRaw_CA hRaw_AF
            have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_lt_trans_DAF hRaw_DA hRaw_AF
            by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
            · -- G strictly outranks F
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
              · -- G ties F
                have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
                refine QuarticSupportCone810.coneFG ?_
                refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
              · -- F strictly outranks G
                have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
                have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
                refine QuarticSupportCone810.coneF ?_
                refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
          · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
            · -- F ties AE
              have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks AEF
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_eq_lt_EAG hEqRaw_EA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FAG hEqRaw_FA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CAG hRaw_CA hRaw_AG
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DAG hRaw_DA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties AEF
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneAEFG ?_
                  refine ⟨hA, hE, hF, hG, quarticEq_EA_of_raw hEqRaw_EA, hEqRaw_FA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, hRaw_DA⟩
                · -- AEF strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneAEF ?_
                  refine ⟨hA, hE, hF, quarticEq_EA_of_raw hEqRaw_EA, hEqRaw_FA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, hRaw_DA, quarticCmp_GA_of_raw hRaw_GA⟩
            · -- AE strictly outranks F
              have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
              have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks AE
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_eq_lt_EAG hEqRaw_EA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CAG hRaw_CA hRaw_AG
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DAG hRaw_DA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FAG hRaw_FA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties AE
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneAEG ?_
                  refine ⟨hA, hE, hG, quarticEq_EA_of_raw hEqRaw_EA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, hRaw_DA, hRaw_FA⟩
                · -- AE strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneAE ?_
                  refine ⟨hA, hE, quarticEq_EA_of_raw hEqRaw_EA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, hRaw_DA, hRaw_FA, quarticCmp_GA_of_raw hRaw_GA⟩
        · -- A strictly outranks E
          have hRed_EA : E.natDegree < 3 * A.natDegree := quarticScore_not_lt_not_eq hAElt hAEeq
          have hRaw_EA : 2 * E.natDegree < 6 * A.natDegree := quarticCmp_EA_to_raw hRed_EA
          by_cases hAFlt : 7 * A.natDegree < 2 * F.natDegree
          · -- F strictly outranks A
            have hRaw_AF : 7 * A.natDegree < 2 * F.natDegree := hAFlt
            have hRaw_BF : 7 * B.natDegree < 3 * F.natDegree := quarticScore_lt_trans_BAF hRaw_BA hRaw_AF
            have hRaw_CF : 7 * C.natDegree < 4 * F.natDegree := quarticScore_lt_trans_CAF hRaw_CA hRaw_AF
            have hRaw_DF : 7 * D.natDegree < 5 * F.natDegree := quarticScore_lt_trans_DAF hRaw_DA hRaw_AF
            have hRaw_EF : 7 * E.natDegree < 6 * F.natDegree := quarticScore_lt_trans_EAF hRaw_EA hRaw_AF
            by_cases hFGlt : 8 * F.natDegree < 7 * G.natDegree
            · -- G strictly outranks F
              have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := hFGlt
              have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticScore_lt_trans_AFG hRaw_AF hRaw_FG
              have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BFG hRaw_BF hRaw_FG
              have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CFG hRaw_CF hRaw_FG
              have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DFG hRaw_DF hRaw_FG
              have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EFG hRaw_EF hRaw_FG
              refine QuarticSupportCone810.coneG ?_
              refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
            · by_cases hFGeq : 8 * F.natDegree = 7 * G.natDegree
              · -- G ties F
                have hEqRaw_GF : 7 * G.natDegree = 8 * F.natDegree := hFGeq.symm
                refine QuarticSupportCone810.coneFG ?_
                refine ⟨hF, hG, hEqRaw_GF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF⟩
              · -- F strictly outranks G
                have hRed_GF : 7 * G.natDegree < 8 * F.natDegree := quarticScore_not_lt_not_eq hFGlt hFGeq
                have hRaw_GF : 7 * G.natDegree < 8 * F.natDegree := hRed_GF
                refine QuarticSupportCone810.coneF ?_
                refine ⟨hF, hRaw_AF, hRaw_BF, hRaw_CF, hRaw_DF, hRaw_EF, hRaw_GF⟩
          · by_cases hAFeq : 7 * A.natDegree = 2 * F.natDegree
            · -- F ties A
              have hEqRaw_FA : 2 * F.natDegree = 7 * A.natDegree := hAFeq.symm
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks AF
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_eq_lt_FAG hEqRaw_FA hRaw_AG
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CAG hRaw_CA hRaw_AG
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DAG hRaw_DA hRaw_AG
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EAG hRaw_EA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties AF
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneAFG ?_
                  refine ⟨hA, hF, hG, hEqRaw_FA, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, hRaw_DA, quarticCmp_EA_of_raw hRaw_EA⟩
                · -- AF strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneAF ?_
                  refine ⟨hA, hF, hEqRaw_FA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, hRaw_DA, quarticCmp_EA_of_raw hRaw_EA, quarticCmp_GA_of_raw hRaw_GA⟩
            · -- A strictly outranks F
              have hRed_FA : 2 * F.natDegree < 7 * A.natDegree := quarticScore_not_lt_not_eq hAFlt hAFeq
              have hRaw_FA : 2 * F.natDegree < 7 * A.natDegree := hRed_FA
              by_cases hAGlt : 4 * A.natDegree < G.natDegree
              · -- G strictly outranks A
                have hRaw_AG : 8 * A.natDegree < 2 * G.natDegree := quarticCmp_AG_to_raw hAGlt
                have hRaw_BG : 8 * B.natDegree < 3 * G.natDegree := quarticScore_lt_trans_BAG hRaw_BA hRaw_AG
                have hRaw_CG : 8 * C.natDegree < 4 * G.natDegree := quarticScore_lt_trans_CAG hRaw_CA hRaw_AG
                have hRaw_DG : 8 * D.natDegree < 5 * G.natDegree := quarticScore_lt_trans_DAG hRaw_DA hRaw_AG
                have hRaw_EG : 8 * E.natDegree < 6 * G.natDegree := quarticScore_lt_trans_EAG hRaw_EA hRaw_AG
                have hRaw_FG : 8 * F.natDegree < 7 * G.natDegree := quarticScore_lt_trans_FAG hRaw_FA hRaw_AG
                refine QuarticSupportCone810.coneG ?_
                refine ⟨hG, quarticCmp_AG_of_raw hRaw_AG, hRaw_BG, quarticCmp_CG_of_raw hRaw_CG, hRaw_DG, quarticCmp_EG_of_raw hRaw_EG, hRaw_FG⟩
              · by_cases hAGeq : 4 * A.natDegree = G.natDegree
                · -- G ties A
                  have hEqRaw_GA : 2 * G.natDegree = 8 * A.natDegree := quarticEq_GA_to_raw (hAGeq.symm)
                  refine QuarticSupportCone810.coneAG ?_
                  refine ⟨hA, hG, quarticEq_GA_of_raw hEqRaw_GA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, hRaw_DA, quarticCmp_EA_of_raw hRaw_EA, hRaw_FA⟩
                · -- A strictly outranks G
                  have hRed_GA : G.natDegree < 4 * A.natDegree := quarticScore_not_lt_not_eq hAGlt hAGeq
                  have hRaw_GA : 2 * G.natDegree < 8 * A.natDegree := quarticCmp_GA_to_raw hRed_GA
                  refine QuarticSupportCone810.coneA ?_
                  refine ⟨hA, hRaw_BA, quarticCmp_CA_of_raw hRaw_CA, hRaw_DA, quarticCmp_EA_of_raw hRaw_EA, hRaw_FA, quarticCmp_GA_of_raw hRaw_GA⟩

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_ABCDEFG_cand_A_rest_CDEFG
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB : 0 < B.natDegree)
    (hC : 0 < C.natDegree)
    (hD : 0 < D.natDegree)
    (hE : 0 < E.natDegree)
    (hF : 0 < F.natDegree)
    (hG : 0 < G.natDegree)
    (hRaw_BA : 2 * B.natDegree < 3 * A.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hAClt : 2 * A.natDegree < C.natDegree
  · -- C strictly outranks A
    have hRaw_AC : 4 * A.natDegree < 2 * C.natDegree := quarticCmp_AC_to_raw hAClt
    have hRaw_BC : 4 * B.natDegree < 3 * C.natDegree := quarticScore_lt_trans_BAC hRaw_BA hRaw_AC
    exact quarticSupportCone810_of_live_ABCDEFG_cand_C_rest_DEFG A B C D E F G hA hB hC hD hE hF hG hRaw_AC hRaw_BC
  · by_cases hACeq : 2 * A.natDegree = C.natDegree
    · -- C ties A
      have hEqRaw_CA : 2 * C.natDegree = 4 * A.natDegree := quarticEq_CA_to_raw (hACeq.symm)
      exact quarticSupportCone810_of_live_ABCDEFG_cand_AC_rest_DEFG A B C D E F G hA hB hC hD hE hF hG hRaw_BA hEqRaw_CA
    · -- A strictly outranks C
      have hRed_CA : C.natDegree < 2 * A.natDegree := quarticScore_not_lt_not_eq hAClt hACeq
      have hRaw_CA : 2 * C.natDegree < 4 * A.natDegree := quarticCmp_CA_to_raw hRed_CA
      exact quarticSupportCone810_of_live_ABCDEFG_cand_A_rest_DEFG A B C D E F G hA hB hC hD hE hF hG hRaw_BA hRaw_CA

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_live_ABCDEFG
    (A B C D E F G : k[X])
    (hA : 0 < A.natDegree)
    (hB : 0 < B.natDegree)
    (hC : 0 < C.natDegree)
    (hD : 0 < D.natDegree)
    (hE : 0 < E.natDegree)
    (hF : 0 < F.natDegree)
    (hG : 0 < G.natDegree) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hABlt : 3 * A.natDegree < 2 * B.natDegree
  · -- B strictly outranks A
    have hRaw_AB : 3 * A.natDegree < 2 * B.natDegree := hABlt
    exact quarticSupportCone810_of_live_ABCDEFG_cand_B_rest_CDEFG A B C D E F G hA hB hC hD hE hF hG hRaw_AB
  · by_cases hABeq : 3 * A.natDegree = 2 * B.natDegree
    · -- B ties A
      have hEqRaw_BA : 2 * B.natDegree = 3 * A.natDegree := hABeq.symm
      exact quarticSupportCone810_of_live_ABCDEFG_cand_AB_rest_CDEFG A B C D E F G hA hB hC hD hE hF hG hEqRaw_BA
    · -- A strictly outranks B
      have hRed_BA : 2 * B.natDegree < 3 * A.natDegree := quarticScore_not_lt_not_eq hABlt hABeq
      have hRaw_BA : 2 * B.natDegree < 3 * A.natDegree := hRed_BA
      exact quarticSupportCone810_of_live_ABCDEFG_cand_A_rest_CDEFG A B C D E F G hA hB hC hD hE hF hG hRaw_BA

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of_allZero
    (A B C D E F G : k[X])
    (hA0 : A.natDegree = 0)
    (hB0 : B.natDegree = 0)
    (hC0 : C.natDegree = 0)
    (hD0 : D.natDegree = 0)
    (hE0 : E.natDegree = 0)
    (hF0 : F.natDegree = 0)
    (hG0 : G.natDegree = 0) :
    QuarticSupportCone810 A B C D E F G :=
  QuarticSupportCone810.allConst ⟨hA0, hB0, hC0, hD0, hE0, hF0, hG0⟩

/-! Combiner. -/

set_option maxHeartbeats 64000000 in
theorem quarticSupportCone810_of (A B C D E F G : k[X]) :
    QuarticSupportCone810 A B C D E F G := by
  by_cases hA : 0 < A.natDegree
  · -- A lives
    by_cases hB : 0 < B.natDegree
    · -- B lives
      by_cases hC : 0 < C.natDegree
      · -- C lives
        by_cases hD : 0 < D.natDegree
        · -- D lives
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABCDEFG A B C D E F G hA hB hC hD hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABCDEF A B C D E F G hA hB hC hD hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABCDEG A B C D E F G hA hB hC hD hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABCDE A B C D E F G hA hB hC hD hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABCDFG A B C D E F G hA hB hC hD hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABCDF A B C D E F G hA hB hC hD hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABCDG A B C D E F G hA hB hC hD hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABCD A B C D E F G hA hB hC hD hE0 hF0 hG0
        · -- D degree 0
          have hD0 : D.natDegree = 0 := Nat.eq_zero_of_not_pos hD
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABCEFG A B C D E F G hA hB hC hD0 hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABCEF A B C D E F G hA hB hC hD0 hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABCEG A B C D E F G hA hB hC hD0 hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABCE A B C D E F G hA hB hC hD0 hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABCFG A B C D E F G hA hB hC hD0 hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABCF A B C D E F G hA hB hC hD0 hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABCG A B C D E F G hA hB hC hD0 hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABC A B C D E F G hA hB hC hD0 hE0 hF0 hG0
      · -- C degree 0
        have hC0 : C.natDegree = 0 := Nat.eq_zero_of_not_pos hC
        by_cases hD : 0 < D.natDegree
        · -- D lives
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABDEFG A B C D E F G hA hB hC0 hD hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABDEF A B C D E F G hA hB hC0 hD hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABDEG A B C D E F G hA hB hC0 hD hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABDE A B C D E F G hA hB hC0 hD hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABDFG A B C D E F G hA hB hC0 hD hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABDF A B C D E F G hA hB hC0 hD hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABDG A B C D E F G hA hB hC0 hD hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABD A B C D E F G hA hB hC0 hD hE0 hF0 hG0
        · -- D degree 0
          have hD0 : D.natDegree = 0 := Nat.eq_zero_of_not_pos hD
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABEFG A B C D E F G hA hB hC0 hD0 hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABEF A B C D E F G hA hB hC0 hD0 hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABEG A B C D E F G hA hB hC0 hD0 hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABE A B C D E F G hA hB hC0 hD0 hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABFG A B C D E F G hA hB hC0 hD0 hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ABF A B C D E F G hA hB hC0 hD0 hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ABG A B C D E F G hA hB hC0 hD0 hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_AB A B C D E F G hA hB hC0 hD0 hE0 hF0 hG0
    · -- B degree 0
      have hB0 : B.natDegree = 0 := Nat.eq_zero_of_not_pos hB
      by_cases hC : 0 < C.natDegree
      · -- C lives
        by_cases hD : 0 < D.natDegree
        · -- D lives
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ACDEFG A B C D E F G hA hB0 hC hD hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ACDEF A B C D E F G hA hB0 hC hD hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ACDEG A B C D E F G hA hB0 hC hD hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ACDE A B C D E F G hA hB0 hC hD hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ACDFG A B C D E F G hA hB0 hC hD hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ACDF A B C D E F G hA hB0 hC hD hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ACDG A B C D E F G hA hB0 hC hD hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ACD A B C D E F G hA hB0 hC hD hE0 hF0 hG0
        · -- D degree 0
          have hD0 : D.natDegree = 0 := Nat.eq_zero_of_not_pos hD
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ACEFG A B C D E F G hA hB0 hC hD0 hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ACEF A B C D E F G hA hB0 hC hD0 hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ACEG A B C D E F G hA hB0 hC hD0 hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ACE A B C D E F G hA hB0 hC hD0 hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ACFG A B C D E F G hA hB0 hC hD0 hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ACF A B C D E F G hA hB0 hC hD0 hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ACG A B C D E F G hA hB0 hC hD0 hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_AC A B C D E F G hA hB0 hC hD0 hE0 hF0 hG0
      · -- C degree 0
        have hC0 : C.natDegree = 0 := Nat.eq_zero_of_not_pos hC
        by_cases hD : 0 < D.natDegree
        · -- D lives
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ADEFG A B C D E F G hA hB0 hC0 hD hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ADEF A B C D E F G hA hB0 hC0 hD hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ADEG A B C D E F G hA hB0 hC0 hD hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ADE A B C D E F G hA hB0 hC0 hD hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ADFG A B C D E F G hA hB0 hC0 hD hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_ADF A B C D E F G hA hB0 hC0 hD hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_ADG A B C D E F G hA hB0 hC0 hD hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_AD A B C D E F G hA hB0 hC0 hD hE0 hF0 hG0
        · -- D degree 0
          have hD0 : D.natDegree = 0 := Nat.eq_zero_of_not_pos hD
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_AEFG A B C D E F G hA hB0 hC0 hD0 hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_AEF A B C D E F G hA hB0 hC0 hD0 hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_AEG A B C D E F G hA hB0 hC0 hD0 hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_AE A B C D E F G hA hB0 hC0 hD0 hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_AFG A B C D E F G hA hB0 hC0 hD0 hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_AF A B C D E F G hA hB0 hC0 hD0 hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_AG A B C D E F G hA hB0 hC0 hD0 hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_A A B C D E F G hA hB0 hC0 hD0 hE0 hF0 hG0
  · -- A degree 0
    have hA0 : A.natDegree = 0 := Nat.eq_zero_of_not_pos hA
    by_cases hB : 0 < B.natDegree
    · -- B lives
      by_cases hC : 0 < C.natDegree
      · -- C lives
        by_cases hD : 0 < D.natDegree
        · -- D lives
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BCDEFG A B C D E F G hA0 hB hC hD hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BCDEF A B C D E F G hA0 hB hC hD hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BCDEG A B C D E F G hA0 hB hC hD hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BCDE A B C D E F G hA0 hB hC hD hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BCDFG A B C D E F G hA0 hB hC hD hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BCDF A B C D E F G hA0 hB hC hD hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BCDG A B C D E F G hA0 hB hC hD hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BCD A B C D E F G hA0 hB hC hD hE0 hF0 hG0
        · -- D degree 0
          have hD0 : D.natDegree = 0 := Nat.eq_zero_of_not_pos hD
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BCEFG A B C D E F G hA0 hB hC hD0 hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BCEF A B C D E F G hA0 hB hC hD0 hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BCEG A B C D E F G hA0 hB hC hD0 hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BCE A B C D E F G hA0 hB hC hD0 hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BCFG A B C D E F G hA0 hB hC hD0 hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BCF A B C D E F G hA0 hB hC hD0 hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BCG A B C D E F G hA0 hB hC hD0 hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BC A B C D E F G hA0 hB hC hD0 hE0 hF0 hG0
      · -- C degree 0
        have hC0 : C.natDegree = 0 := Nat.eq_zero_of_not_pos hC
        by_cases hD : 0 < D.natDegree
        · -- D lives
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BDEFG A B C D E F G hA0 hB hC0 hD hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BDEF A B C D E F G hA0 hB hC0 hD hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BDEG A B C D E F G hA0 hB hC0 hD hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BDE A B C D E F G hA0 hB hC0 hD hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BDFG A B C D E F G hA0 hB hC0 hD hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BDF A B C D E F G hA0 hB hC0 hD hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BDG A B C D E F G hA0 hB hC0 hD hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BD A B C D E F G hA0 hB hC0 hD hE0 hF0 hG0
        · -- D degree 0
          have hD0 : D.natDegree = 0 := Nat.eq_zero_of_not_pos hD
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BEFG A B C D E F G hA0 hB hC0 hD0 hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BEF A B C D E F G hA0 hB hC0 hD0 hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BEG A B C D E F G hA0 hB hC0 hD0 hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BE A B C D E F G hA0 hB hC0 hD0 hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BFG A B C D E F G hA0 hB hC0 hD0 hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_BF A B C D E F G hA0 hB hC0 hD0 hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_BG A B C D E F G hA0 hB hC0 hD0 hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_B A B C D E F G hA0 hB hC0 hD0 hE0 hF0 hG0
    · -- B degree 0
      have hB0 : B.natDegree = 0 := Nat.eq_zero_of_not_pos hB
      by_cases hC : 0 < C.natDegree
      · -- C lives
        by_cases hD : 0 < D.natDegree
        · -- D lives
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_CDEFG A B C D E F G hA0 hB0 hC hD hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_CDEF A B C D E F G hA0 hB0 hC hD hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_CDEG A B C D E F G hA0 hB0 hC hD hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_CDE A B C D E F G hA0 hB0 hC hD hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_CDFG A B C D E F G hA0 hB0 hC hD hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_CDF A B C D E F G hA0 hB0 hC hD hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_CDG A B C D E F G hA0 hB0 hC hD hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_CD A B C D E F G hA0 hB0 hC hD hE0 hF0 hG0
        · -- D degree 0
          have hD0 : D.natDegree = 0 := Nat.eq_zero_of_not_pos hD
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_CEFG A B C D E F G hA0 hB0 hC hD0 hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_CEF A B C D E F G hA0 hB0 hC hD0 hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_CEG A B C D E F G hA0 hB0 hC hD0 hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_CE A B C D E F G hA0 hB0 hC hD0 hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_CFG A B C D E F G hA0 hB0 hC hD0 hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_CF A B C D E F G hA0 hB0 hC hD0 hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_CG A B C D E F G hA0 hB0 hC hD0 hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_C A B C D E F G hA0 hB0 hC hD0 hE0 hF0 hG0
      · -- C degree 0
        have hC0 : C.natDegree = 0 := Nat.eq_zero_of_not_pos hC
        by_cases hD : 0 < D.natDegree
        · -- D lives
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_DEFG A B C D E F G hA0 hB0 hC0 hD hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_DEF A B C D E F G hA0 hB0 hC0 hD hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_DEG A B C D E F G hA0 hB0 hC0 hD hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_DE A B C D E F G hA0 hB0 hC0 hD hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_DFG A B C D E F G hA0 hB0 hC0 hD hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_DF A B C D E F G hA0 hB0 hC0 hD hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_DG A B C D E F G hA0 hB0 hC0 hD hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_D A B C D E F G hA0 hB0 hC0 hD hE0 hF0 hG0
        · -- D degree 0
          have hD0 : D.natDegree = 0 := Nat.eq_zero_of_not_pos hD
          by_cases hE : 0 < E.natDegree
          · -- E lives
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_EFG A B C D E F G hA0 hB0 hC0 hD0 hE hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_EF A B C D E F G hA0 hB0 hC0 hD0 hE hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_EG A B C D E F G hA0 hB0 hC0 hD0 hE hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_E A B C D E F G hA0 hB0 hC0 hD0 hE hF0 hG0
          · -- E degree 0
            have hE0 : E.natDegree = 0 := Nat.eq_zero_of_not_pos hE
            by_cases hF : 0 < F.natDegree
            · -- F lives
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_FG A B C D E F G hA0 hB0 hC0 hD0 hE0 hF hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_live_F A B C D E F G hA0 hB0 hC0 hD0 hE0 hF hG0
            · -- F degree 0
              have hF0 : F.natDegree = 0 := Nat.eq_zero_of_not_pos hF
              by_cases hG : 0 < G.natDegree
              · -- G lives
                exact quarticSupportCone810_of_live_G A B C D E F G hA0 hB0 hC0 hD0 hE0 hF0 hG
              · -- G degree 0
                have hG0 : G.natDegree = 0 := Nat.eq_zero_of_not_pos hG
                exact quarticSupportCone810_of_allZero A B C D E F G hA0 hB0 hC0 hD0 hE0 hF0 hG0

/-! ## Stage A residual -/

end QuarticExhaust810

end Max11DegreeRoutes
