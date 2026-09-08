import Grok610ScaleZeroCubicConesSpeedReflValDegSplitPart15oScratch

noncomputable section

open scoped Polynomial.Bivariate
open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 8000000

section CubicExhaust610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in

theorem cubicSupportCone610_of (A B C D E : k[X]) :
    CubicSupportCone610 A B C D E := by
  by_cases hABlt : 3 * A.natDegree < 2 * B.natDegree
  · -- B strictly outranks A
    by_cases hBClt : 4 * B.natDegree < 3 * C.natDegree
    · -- C strictly outranks B
      by_cases hCDlt : 5 * C.natDegree < 4 * D.natDegree
      · -- D strictly outranks C
        by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
        · -- E strictly outranks D
          by_cases hpos : 0 < E.natDegree
          · -- nonempty cone E
            refine CubicSupportCone610.coneE ?_
            refine ⟨by omega, by omega, by omega, by omega, by omega⟩
          · -- ruler degree 0 ⇒ all constant
            refine CubicSupportCone610.allConst ?_
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · omega
            · omega
            · omega
            · omega
            · omega
        · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
          · -- E ties D
            by_cases hpos : 0 < D.natDegree
            · -- nonempty cone DE
              refine CubicSupportCone610.coneDE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
          · -- D strictly outranks E
            by_cases hpos : 0 < D.natDegree
            · -- nonempty cone D
              refine CubicSupportCone610.coneD ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
      · by_cases hCDeq : 5 * C.natDegree = 4 * D.natDegree
        · -- D ties C
          by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
          · -- E strictly outranks CD
            by_cases hpos : 0 < E.natDegree
            · -- nonempty cone E
              refine CubicSupportCone610.coneE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
          · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
            · -- E ties CD
              by_cases hpos : 0 < C.natDegree
              · -- nonempty cone CDE
                refine CubicSupportCone610.coneCDE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · -- CD strictly outranks E
              by_cases hpos : 0 < C.natDegree
              · -- nonempty cone CD
                refine CubicSupportCone610.coneCD ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
        · -- C strictly outranks D
          by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
          · -- E strictly outranks C
            by_cases hpos : 0 < E.natDegree
            · -- nonempty cone E
              refine CubicSupportCone610.coneE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
          · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
            · -- E ties C
              by_cases hpos : 0 < C.natDegree
              · -- nonempty cone CE
                refine CubicSupportCone610.coneCE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · -- C strictly outranks E
              by_cases hpos : 0 < C.natDegree
              · -- nonempty cone C
                refine CubicSupportCone610.coneC ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
    · by_cases hBCeq : 4 * B.natDegree = 3 * C.natDegree
      · -- C ties B
        by_cases hBDlt : 5 * B.natDegree < 3 * D.natDegree
        · -- D strictly outranks BC
          by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
          · -- E strictly outranks D
            by_cases hpos : 0 < E.natDegree
            · -- nonempty cone E
              refine CubicSupportCone610.coneE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
          · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
            · -- E ties D
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone DE
                refine CubicSupportCone610.coneDE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · -- D strictly outranks E
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone D
                refine CubicSupportCone610.coneD ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
        · by_cases hBDeq : 5 * B.natDegree = 3 * D.natDegree
          · -- D ties BC
            by_cases hBElt : 2 * B.natDegree < E.natDegree
            · -- E strictly outranks BCD
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hBEeq : 2 * B.natDegree = E.natDegree
              · -- E ties BCD
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone BCDE
                  refine CubicSupportCone610.coneBCDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- BCD strictly outranks E
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone BCD
                  refine CubicSupportCone610.coneBCD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · -- BC strictly outranks D
            by_cases hBElt : 2 * B.natDegree < E.natDegree
            · -- E strictly outranks BC
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hBEeq : 2 * B.natDegree = E.natDegree
              · -- E ties BC
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone BCE
                  refine CubicSupportCone610.coneBCE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- BC strictly outranks E
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone BC
                  refine CubicSupportCone610.coneBC ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
      · -- B strictly outranks C
        by_cases hBDlt : 5 * B.natDegree < 3 * D.natDegree
        · -- D strictly outranks B
          by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
          · -- E strictly outranks D
            by_cases hpos : 0 < E.natDegree
            · -- nonempty cone E
              refine CubicSupportCone610.coneE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
          · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
            · -- E ties D
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone DE
                refine CubicSupportCone610.coneDE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · -- D strictly outranks E
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone D
                refine CubicSupportCone610.coneD ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
        · by_cases hBDeq : 5 * B.natDegree = 3 * D.natDegree
          · -- D ties B
            by_cases hBElt : 2 * B.natDegree < E.natDegree
            · -- E strictly outranks BD
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hBEeq : 2 * B.natDegree = E.natDegree
              · -- E ties BD
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone BDE
                  refine CubicSupportCone610.coneBDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- BD strictly outranks E
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone BD
                  refine CubicSupportCone610.coneBD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · -- B strictly outranks D
            by_cases hBElt : 2 * B.natDegree < E.natDegree
            · -- E strictly outranks B
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hBEeq : 2 * B.natDegree = E.natDegree
              · -- E ties B
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone BE
                  refine CubicSupportCone610.coneBE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- B strictly outranks E
                by_cases hpos : 0 < B.natDegree
                · -- nonempty cone B
                  refine CubicSupportCone610.coneB ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
  · by_cases hABeq : 3 * A.natDegree = 2 * B.natDegree
    · -- B ties A
      by_cases hAClt : 2 * A.natDegree < C.natDegree
      · -- C strictly outranks AB
        by_cases hCDlt : 5 * C.natDegree < 4 * D.natDegree
        · -- D strictly outranks C
          by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
          · -- E strictly outranks D
            by_cases hpos : 0 < E.natDegree
            · -- nonempty cone E
              refine CubicSupportCone610.coneE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
          · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
            · -- E ties D
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone DE
                refine CubicSupportCone610.coneDE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · -- D strictly outranks E
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone D
                refine CubicSupportCone610.coneD ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
        · by_cases hCDeq : 5 * C.natDegree = 4 * D.natDegree
          · -- D ties C
            by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
            · -- E strictly outranks CD
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
              · -- E ties CD
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone CDE
                  refine CubicSupportCone610.coneCDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- CD strictly outranks E
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone CD
                  refine CubicSupportCone610.coneCD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · -- C strictly outranks D
            by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
            · -- E strictly outranks C
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
              · -- E ties C
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone CE
                  refine CubicSupportCone610.coneCE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- C strictly outranks E
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone C
                  refine CubicSupportCone610.coneC ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
      · by_cases hACeq : 2 * A.natDegree = C.natDegree
        · -- C ties AB
          by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
          · -- D strictly outranks ABC
            by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
            · -- E strictly outranks D
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
              · -- E ties D
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone DE
                  refine CubicSupportCone610.coneDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- D strictly outranks E
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone D
                  refine CubicSupportCone610.coneD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
            · -- D ties ABC
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks ABCD
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties ABCD
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ABCDE
                    refine CubicSupportCone610.coneABCDE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- ABCD strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ABCD
                    refine CubicSupportCone610.coneABCD ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
            · -- ABC strictly outranks D
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks ABC
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties ABC
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ABCE
                    refine CubicSupportCone610.coneABCE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- ABC strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ABC
                    refine CubicSupportCone610.coneABC ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
        · -- AB strictly outranks C
          by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
          · -- D strictly outranks AB
            by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
            · -- E strictly outranks D
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
              · -- E ties D
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone DE
                  refine CubicSupportCone610.coneDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- D strictly outranks E
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone D
                  refine CubicSupportCone610.coneD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
            · -- D ties AB
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks ABD
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties ABD
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ABDE
                    refine CubicSupportCone610.coneABDE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- ABD strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ABD
                    refine CubicSupportCone610.coneABD ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
            · -- AB strictly outranks D
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks AB
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties AB
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ABE
                    refine CubicSupportCone610.coneABE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- AB strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone AB
                    refine CubicSupportCone610.coneAB ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
    · -- A strictly outranks B
      by_cases hAClt : 2 * A.natDegree < C.natDegree
      · -- C strictly outranks A
        by_cases hCDlt : 5 * C.natDegree < 4 * D.natDegree
        · -- D strictly outranks C
          by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
          · -- E strictly outranks D
            by_cases hpos : 0 < E.natDegree
            · -- nonempty cone E
              refine CubicSupportCone610.coneE ?_
              refine ⟨by omega, by omega, by omega, by omega, by omega⟩
            · -- ruler degree 0 ⇒ all constant
              refine CubicSupportCone610.allConst ?_
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · omega
              · omega
              · omega
              · omega
              · omega
          · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
            · -- E ties D
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone DE
                refine CubicSupportCone610.coneDE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · -- D strictly outranks E
              by_cases hpos : 0 < D.natDegree
              · -- nonempty cone D
                refine CubicSupportCone610.coneD ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
        · by_cases hCDeq : 5 * C.natDegree = 4 * D.natDegree
          · -- D ties C
            by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
            · -- E strictly outranks CD
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
              · -- E ties CD
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone CDE
                  refine CubicSupportCone610.coneCDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- CD strictly outranks E
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone CD
                  refine CubicSupportCone610.coneCD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · -- C strictly outranks D
            by_cases hCElt : 3 * C.natDegree < 2 * E.natDegree
            · -- E strictly outranks C
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hCEeq : 3 * C.natDegree = 2 * E.natDegree
              · -- E ties C
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone CE
                  refine CubicSupportCone610.coneCE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- C strictly outranks E
                by_cases hpos : 0 < C.natDegree
                · -- nonempty cone C
                  refine CubicSupportCone610.coneC ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
      · by_cases hACeq : 2 * A.natDegree = C.natDegree
        · -- C ties A
          by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
          · -- D strictly outranks AC
            by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
            · -- E strictly outranks D
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
              · -- E ties D
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone DE
                  refine CubicSupportCone610.coneDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- D strictly outranks E
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone D
                  refine CubicSupportCone610.coneD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
            · -- D ties AC
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks ACD
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties ACD
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ACDE
                    refine CubicSupportCone610.coneACDE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- ACD strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ACD
                    refine CubicSupportCone610.coneACD ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
            · -- AC strictly outranks D
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks AC
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties AC
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ACE
                    refine CubicSupportCone610.coneACE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- AC strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone AC
                    refine CubicSupportCone610.coneAC ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
        · -- A strictly outranks C
          by_cases hADlt : 5 * A.natDegree < 2 * D.natDegree
          · -- D strictly outranks A
            by_cases hDElt : 6 * D.natDegree < 5 * E.natDegree
            · -- E strictly outranks D
              by_cases hpos : 0 < E.natDegree
              · -- nonempty cone E
                refine CubicSupportCone610.coneE ?_
                refine ⟨by omega, by omega, by omega, by omega, by omega⟩
              · -- ruler degree 0 ⇒ all constant
                refine CubicSupportCone610.allConst ?_
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · omega
                · omega
                · omega
                · omega
                · omega
            · by_cases hDEeq : 6 * D.natDegree = 5 * E.natDegree
              · -- E ties D
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone DE
                  refine CubicSupportCone610.coneDE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · -- D strictly outranks E
                by_cases hpos : 0 < D.natDegree
                · -- nonempty cone D
                  refine CubicSupportCone610.coneD ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
          · by_cases hADeq : 5 * A.natDegree = 2 * D.natDegree
            · -- D ties A
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks AD
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties AD
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone ADE
                    refine CubicSupportCone610.coneADE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- AD strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone AD
                    refine CubicSupportCone610.coneAD ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
            · -- A strictly outranks D
              by_cases hAElt : 3 * A.natDegree < E.natDegree
              · -- E strictly outranks A
                by_cases hpos : 0 < E.natDegree
                · -- nonempty cone E
                  refine CubicSupportCone610.coneE ?_
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                · -- ruler degree 0 ⇒ all constant
                  refine CubicSupportCone610.allConst ?_
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · omega
                  · omega
                  · omega
                  · omega
                  · omega
              · by_cases hAEeq : 3 * A.natDegree = E.natDegree
                · -- E ties A
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone AE
                    refine CubicSupportCone610.coneAE ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega
                · -- A strictly outranks E
                  by_cases hpos : 0 < A.natDegree
                  · -- nonempty cone A
                    refine CubicSupportCone610.coneA ?_
                    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                  · -- ruler degree 0 ⇒ all constant
                    refine CubicSupportCone610.allConst ?_
                    refine ⟨?_, ?_, ?_, ?_, ?_⟩
                    · omega
                    · omega
                    · omega
                    · omega
                    · omega

end CubicExhaust610

end Max11DegreeRoutes

end
