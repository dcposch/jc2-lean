import Grok610ScaleZeroCubicLoadWallsPart176Scratch
import Grok610ScaleZeroCubicLoadWallsPart177Scratch
import Grok610ScaleZeroCubicLoadWallsPart178Scratch
import Grok610ScaleZeroCubicLoadWallsPart179Scratch
import Grok610ScaleZeroCubicLoadWallsPart200Scratch

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
set_option maxRecDepth 100000000

section CubicLoadWallsAssembly610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem cubicLoadSigmaCone_CD_impossible {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeCD610 A B C D E)
    (hl : l = 0)
    (hb4 : (beta = 0 ∨
      7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree))
    (hd4 : (delta = 0 ∨
      7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree))
    (hz4 : (zeta = 0 ∨
      9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
      10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
      12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree))
    (ht4 : (theta = 0 ∨
      7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
      7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
      7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree))
    (hlam : (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (homi : (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  by_cases hch : 2 * C.natDegree + D.natDegree ≤ A.natDegree
  · exact cubicLoadSigmaCone_CD_chamber_impossible (j := j) (t := t) l
      alpha beta delta epsilon zeta eta theta A B C D E hcone hl hch
      hmu hkap hlam homi
  · have hTpos : A.natDegree < 2 * C.natDegree + D.natDegree :=
      lt_of_not_ge hch
    have hb := cubicLoadSigmaConeCD610_specialize_beta hcone hb4
    have hd := cubicLoadSigmaConeCD610_specialize_delta hcone hd4
    have hz := cubicLoadSigmaConeCD610_specialize_zeta hcone hz4
    have ht := cubicLoadSigmaConeCD610_specialize_theta hcone ht4
    rcases hb with hb0 | hble
    · rcases hd with hd0 | hdle
      · rcases hz with hz0 | hzle
        · rcases ht with ht0 | htle
          · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
              delta epsilon zeta eta theta A B C D E hcone hl (Or.inl hb0)
              (Or.inl hd0) (Or.inl hz0) (Or.inl ht0) hTpos hmu hkap
          · rcases lt_or_eq_of_le htle with htlt | hteq
            · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                delta epsilon zeta eta theta A B C D E hcone hl
                (Or.inl hb0) (Or.inl hd0) (Or.inl hz0) (Or.inr htlt)
                hTpos hmu hkap
            · exact cubicLoadSigmaCone_CD_thetaWall_impossible (j := j)
                (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                hcone hl hteq hmu hkap hjdiv hder
        · rcases lt_or_eq_of_le hzle with hzlt | hzeq
          · rcases ht with ht0 | htle
            · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                delta epsilon zeta eta theta A B C D E hcone hl
                (Or.inl hb0) (Or.inl hd0) (Or.inr hzlt) (Or.inl ht0)
                hTpos hmu hkap
            · rcases lt_or_eq_of_le htle with htlt | hteq
              · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                  delta epsilon zeta eta theta A B C D E hcone hl
                  (Or.inl hb0) (Or.inl hd0) (Or.inr hzlt) (Or.inr htlt)
                  hTpos hmu hkap
              · exact cubicLoadSigmaCone_CD_thetaWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta
                  A B C D E hcone hl hteq hmu hkap hjdiv hder
          · exact cubicLoadSigmaCone_CD_zetaWall_impossible (j := j)
              (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
              hcone hl hzeq hmu hkap hjdiv hder
      · rcases lt_or_eq_of_le hdle with hdlt | hdeq
        · rcases hz with hz0 | hzle
          · rcases ht with ht0 | htle
            · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                delta epsilon zeta eta theta A B C D E hcone hl
                (Or.inl hb0) (Or.inr hdlt) (Or.inl hz0) (Or.inl ht0)
                hTpos hmu hkap
            · rcases lt_or_eq_of_le htle with htlt | hteq
              · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                  delta epsilon zeta eta theta A B C D E hcone hl
                  (Or.inl hb0) (Or.inr hdlt) (Or.inl hz0) (Or.inr htlt)
                  hTpos hmu hkap
              · exact cubicLoadSigmaCone_CD_thetaWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta
                  A B C D E hcone hl hteq hmu hkap hjdiv hder
          · rcases lt_or_eq_of_le hzle with hzlt | hzeq
            · rcases ht with ht0 | htle
              · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                  delta epsilon zeta eta theta A B C D E hcone hl
                  (Or.inl hb0) (Or.inr hdlt) (Or.inr hzlt) (Or.inl ht0)
                  hTpos hmu hkap
              · rcases lt_or_eq_of_le htle with htlt | hteq
                · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha
                    beta delta epsilon zeta eta theta A B C D E hcone hl
                    (Or.inl hb0) (Or.inr hdlt) (Or.inr hzlt) (Or.inr htlt)
                    hTpos hmu hkap
                · exact cubicLoadSigmaCone_CD_thetaWall_impossible (j := j)
                    (t := t) l alpha beta delta epsilon zeta eta theta
                    A B C D E hcone hl hteq hmu hkap hjdiv hder
            · exact cubicLoadSigmaCone_CD_zetaWall_impossible (j := j)
                (t := t) l alpha beta delta epsilon zeta eta theta
                A B C D E hcone hl hzeq hmu hkap hjdiv hder
        · exact cubicLoadSigmaCone_CD_deltaWall_impossible (j := j)
            (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
            hcone hl hdeq hmu hkap hjdiv hder
    · rcases lt_or_eq_of_le hble with hblt | hbeq
      · rcases hd with hd0 | hdle
        · rcases hz with hz0 | hzle
          · rcases ht with ht0 | htle
            · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                delta epsilon zeta eta theta A B C D E hcone hl
                (Or.inr hblt) (Or.inl hd0) (Or.inl hz0) (Or.inl ht0)
                hTpos hmu hkap
            · rcases lt_or_eq_of_le htle with htlt | hteq
              · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                  delta epsilon zeta eta theta A B C D E hcone hl
                  (Or.inr hblt) (Or.inl hd0) (Or.inl hz0) (Or.inr htlt)
                  hTpos hmu hkap
              · exact cubicLoadSigmaCone_CD_thetaWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta
                  A B C D E hcone hl hteq hmu hkap hjdiv hder
          · rcases lt_or_eq_of_le hzle with hzlt | hzeq
            · rcases ht with ht0 | htle
              · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                  delta epsilon zeta eta theta A B C D E hcone hl
                  (Or.inr hblt) (Or.inl hd0) (Or.inr hzlt) (Or.inl ht0)
                  hTpos hmu hkap
              · rcases lt_or_eq_of_le htle with htlt | hteq
                · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha
                    beta delta epsilon zeta eta theta A B C D E hcone hl
                    (Or.inr hblt) (Or.inl hd0) (Or.inr hzlt) (Or.inr htlt)
                    hTpos hmu hkap
                · exact cubicLoadSigmaCone_CD_thetaWall_impossible (j := j)
                    (t := t) l alpha beta delta epsilon zeta eta theta
                    A B C D E hcone hl hteq hmu hkap hjdiv hder
            · exact cubicLoadSigmaCone_CD_zetaWall_impossible (j := j)
                (t := t) l alpha beta delta epsilon zeta eta theta
                A B C D E hcone hl hzeq hmu hkap hjdiv hder
        · rcases lt_or_eq_of_le hdle with hdlt | hdeq
          · rcases hz with hz0 | hzle
            · rcases ht with ht0 | htle
              · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha beta
                  delta epsilon zeta eta theta A B C D E hcone hl
                  (Or.inr hblt) (Or.inr hdlt) (Or.inl hz0) (Or.inl ht0)
                  hTpos hmu hkap
              · rcases lt_or_eq_of_le htle with htlt | hteq
                · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha
                    beta delta epsilon zeta eta theta A B C D E hcone hl
                    (Or.inr hblt) (Or.inr hdlt) (Or.inl hz0) (Or.inr htlt)
                    hTpos hmu hkap
                · exact cubicLoadSigmaCone_CD_thetaWall_impossible (j := j)
                    (t := t) l alpha beta delta epsilon zeta eta theta
                    A B C D E hcone hl hteq hmu hkap hjdiv hder
            · rcases lt_or_eq_of_le hzle with hzlt | hzeq
              · rcases ht with ht0 | htle
                · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha
                    beta delta epsilon zeta eta theta A B C D E hcone hl
                    (Or.inr hblt) (Or.inr hdlt) (Or.inr hzlt) (Or.inl ht0)
                    hTpos hmu hkap
                · rcases lt_or_eq_of_le htle with htlt | hteq
                  · exact cubicLoadSigmaCone_CD_offWall_impossible l alpha
                      beta delta epsilon zeta eta theta A B C D E hcone hl
                      (Or.inr hblt) (Or.inr hdlt) (Or.inr hzlt)
                      (Or.inr htlt) hTpos hmu hkap
                  · exact cubicLoadSigmaCone_CD_thetaWall_impossible
                      (j := j) (t := t) l alpha beta delta epsilon zeta
                      eta theta A B C D E hcone hl hteq hmu hkap hjdiv hder
              · exact cubicLoadSigmaCone_CD_zetaWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta
                  A B C D E hcone hl hzeq hmu hkap hjdiv hder
          · exact cubicLoadSigmaCone_CD_deltaWall_impossible (j := j)
              (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
              hcone hl hdeq hmu hkap hjdiv hder
      · exact cubicLoadSigmaCone_CD_betaWall_impossible (j := j) (t := t)
          l alpha beta delta epsilon zeta eta theta A B C D E hcone hl
          hbeq hmu hkap hjdiv hder

end CubicLoadWallsAssembly610

end Max11DegreeRoutes
