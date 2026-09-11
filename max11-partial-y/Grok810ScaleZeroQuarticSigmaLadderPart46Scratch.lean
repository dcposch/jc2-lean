import Grok810ScaleZeroQuarticSigmaLadderPart43Scratch

/-! Part 46 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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

variable {k : Type*} [Field k] [CharZero k]

section QuarticKappaLadder810


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoL1810_natDegree_lt_of_lTop
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < 5 * A.natDegree)
    (hCt : 4 * C.natDegree < 7 * A.natDegree)
    (hDt : 4 * D.natDegree < 9 * A.natDegree)
    (hEt : 4 * E.natDegree < 11 * A.natDegree)
    (hFt : 4 * F.natDegree < 13 * A.natDegree)
    (hGt : 4 * G.natDegree < 15 * A.natDegree) :
    (degreeZeroKappaQuarticNoL1810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hAF
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hAG
  have hBt1 : 4 * B.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hBt
  have hCt1 : 4 * C.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hCt
  have hDt1 : 4 * D.natDegree + 1 ≤ 9 * A.natDegree := Nat.succ_le_of_lt hDt
  have hEt1 : 4 * E.natDegree + 1 ≤ 11 * A.natDegree := Nat.succ_le_of_lt hEt
  have hFt1 : 4 * F.natDegree + 1 ≤ 13 * A.natDegree := Nat.succ_le_of_lt hFt
  have hGt1 : 4 * G.natDegree + 1 ≤ 15 * A.natDegree := Nat.succ_le_of_lt hGt
  simp only [degreeZeroKappaQuarticNoL1810]
  compute_degree
  omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaQuarticNoL2810_natDegree_lt_of_lTop
    (l beta gamma delta epsilon zeta eta theta : k)
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hAB : 2 * B.natDegree < 3 * A.natDegree)
    (hAC : C.natDegree < 2 * A.natDegree)
    (hAD : 2 * D.natDegree < 5 * A.natDegree)
    (hAE : E.natDegree < 3 * A.natDegree)
    (hAF : 2 * F.natDegree < 7 * A.natDegree)
    (hAG : G.natDegree < 4 * A.natDegree)
    (hBt : 4 * B.natDegree < 5 * A.natDegree)
    (hCt : 4 * C.natDegree < 7 * A.natDegree)
    (hDt : 4 * D.natDegree < 9 * A.natDegree)
    (hEt : 4 * E.natDegree < 11 * A.natDegree)
    (hFt : 4 * F.natDegree < 13 * A.natDegree)
    (hGt : 4 * G.natDegree < 15 * A.natDegree) :
    (degreeZeroKappaQuarticNoL2810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      5 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hAF
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hAG
  have hBt1 : 4 * B.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hBt
  have hCt1 : 4 * C.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hCt
  have hDt1 : 4 * D.natDegree + 1 ≤ 9 * A.natDegree := Nat.succ_le_of_lt hDt
  have hEt1 : 4 * E.natDegree + 1 ≤ 11 * A.natDegree := Nat.succ_le_of_lt hEt
  have hFt1 : 4 * F.natDegree + 1 ≤ 13 * A.natDegree := Nat.succ_le_of_lt hFt
  have hGt1 : 4 * G.natDegree + 1 ≤ 15 * A.natDegree := Nat.succ_le_of_lt hGt
  simp only [degreeZeroKappaQuarticNoL2810]
  compute_degree
  omega


end QuarticKappaLadder810
end Max11DegreeRoutes
end
