import Grok610ScaleZeroCubicLoadMultiPart09Scratch
import Grok610ScaleZeroCubicLoadMultiPart10Scratch
import Grok610ScaleZeroCubicLoadMultiPart11Scratch
import Grok610ScaleZeroCubicLoadMultiPart12Scratch
import Grok610ScaleZeroCubicLoadMultiPart33Scratch
import Grok610ScaleZeroCubicLoadMultiPart37Scratch
import Grok610ScaleZeroCubicLoadMultiPart42Scratch

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

section CubicLoadMultiAssembly610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
theorem normalized610ScaleZero_cubicResidual8
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota cLam cKap cMu cOmi : k) (A B C D E : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta
            eta theta A B C D E) =
        Polynomial.C (j / t) ∧
      (degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      (degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree = 0 ∧
      CubicRatioConeA610 A B C D E ∧
      cubicLoadCompetes610 A B C D E ∧
      l = 0 ∧
      (cubicKappaBetaTop610 A B C D E → beta = 0) ∧
      (cubicKappaDeltaTop610 A B C D E → delta = 0) ∧
      (cubicKappaZetaTop610 A B C D E → zeta = 0) ∧
      (cubicN1BetaTop610 A B C D E → beta = 0) ∧
      (cubicN1DeltaTop610 A B C D E → delta = 0) ∧
      (cubicN1ZetaTop610 A B C D E → zeta = 0) ∧
      (cubicN1ThetaTop610 A B C D E → theta = 0) ∧
      (beta = 0 ∨
        7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree ∨
        7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 42 * C.natDegree ∨
        7 * (10 * A.natDegree) ≤ 18 * A.natDegree + 28 * D.natDegree ∨
        7 * (12 * A.natDegree) ≤ 18 * A.natDegree + 28 * E.natDegree) ∧
      (delta = 0 ∨
        7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree ∨
        7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 42 * C.natDegree ∨
        7 * (10 * A.natDegree) ≤ 30 * A.natDegree + 28 * D.natDegree ∨
        7 * (12 * A.natDegree) ≤ 30 * A.natDegree + 28 * E.natDegree) ∧
      (zeta = 0 ∨
        9 * A.natDegree ≤ 6 * A.natDegree + 6 * B.natDegree ∨
        12 * A.natDegree ≤ 6 * A.natDegree + 6 * C.natDegree ∨
        10 * A.natDegree ≤ 6 * A.natDegree + 4 * D.natDegree ∨
        12 * A.natDegree ≤ 6 * A.natDegree + 4 * E.natDegree) ∧
      (theta = 0 ∨
        7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree ∨
        7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 42 * C.natDegree ∨
        7 * (10 * A.natDegree) ≤ 54 * A.natDegree + 28 * D.natDegree ∨
        7 * (12 * A.natDegree) ≤ 54 * A.natDegree + 28 * E.natDegree) ∧
      (CubicLoadSigmaConeCD610 A B C D E ∨
        (CubicLoadSigmaConeBCDE610 A B C D E ∧
          (7 * (9 * A.natDegree) = 18 * A.natDegree + 42 * B.natDegree ∨
            7 * (9 * A.natDegree) = 30 * A.natDegree + 42 * B.natDegree ∨
            9 * A.natDegree = 6 * A.natDegree + 6 * B.natDegree ∨
            7 * (9 * A.natDegree) = 54 * A.natDegree + 42 * B.natDegree))) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht,
      hj, hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA,
      hload, hl0, hkapB, hkapD, hkapZ, hbN1, hdN1, hzN1, htN1, hbBand,
      hdBand, hzBand, htBand, hexh⟩ :=
    normalized610ScaleZero_cubicResidual7 hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, cLam, cKap, cMu, cOmi, A, B, C, D, E, ht, hj,
    hjdiv, hHsq, hder, hlamDeg, hkapDeg, hmuDeg, homiDeg, hconeA, hload,
    hl0, hkapB, hkapD, hkapZ, hbN1, hdN1, hzN1, htN1, hbBand, hdBand,
    hzBand, htBand, ?_⟩
  rcases hexh with hBC | hBCE | hBCDE | hCD
  · exact (cubicLoadSigmaCone_BC_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hBC hl0 hbBand hdBand hzBand
      htBand hlamDeg hkapDeg).elim
  · exact (cubicLoadSigmaCone_BCE_impossible (j := j) (t := t) l alpha beta
      delta epsilon zeta eta theta A B C D E hBCE hl0 hbBand hdBand hzBand
      htBand hlamDeg hkapDeg homiDeg).elim
  · -- `{B,C,D,E}`: off-wall identity, else an N₁ wall.
    have hb := cubicLoadSigmaConeBCDE610_specialize_beta hBCDE hbBand
    have hd := cubicLoadSigmaConeBCDE610_specialize_delta hBCDE hdBand
    have hz := cubicLoadSigmaConeBCDE610_specialize_zeta hBCDE hzBand
    have ht := cubicLoadSigmaConeBCDE610_specialize_theta hBCDE htBand
    rcases hb with hb0 | hble
    · rcases hd with hd0 | hdle
      · rcases hz with hz0 | hzle
        · rcases ht with ht0 | htle
          · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
              (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
              hBCDE hl0 (Or.inl hb0) (Or.inl hd0) (Or.inl hz0) (Or.inl ht0)
              hlamDeg hkapDeg hmuDeg homiDeg).elim
          · rcases lt_or_eq_of_le htle with htlt | hteq
            · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                hBCDE hl0 (Or.inl hb0) (Or.inl hd0) (Or.inl hz0) (Or.inr htlt)
                hlamDeg hkapDeg hmuDeg homiDeg).elim
            · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
        · rcases lt_or_eq_of_le hzle with hzlt | hzeq
          · rcases ht with ht0 | htle
            · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                hBCDE hl0 (Or.inl hb0) (Or.inl hd0) (Or.inr hzlt)
                (Or.inl ht0) hlamDeg hkapDeg hmuDeg homiDeg).elim
            · rcases lt_or_eq_of_le htle with htlt | hteq
              · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                  hBCDE hl0 (Or.inl hb0) (Or.inl hd0) (Or.inr hzlt)
                  (Or.inr htlt) hlamDeg hkapDeg hmuDeg homiDeg).elim
              · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
          · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inl hzeq))⟩
      · rcases lt_or_eq_of_le hdle with hdlt | hdeq
        · rcases hz with hz0 | hzle
          · rcases ht with ht0 | htle
            · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                hBCDE hl0 (Or.inl hb0) (Or.inr hdlt) (Or.inl hz0)
                (Or.inl ht0) hlamDeg hkapDeg hmuDeg homiDeg).elim
            · rcases lt_or_eq_of_le htle with htlt | hteq
              · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                  hBCDE hl0 (Or.inl hb0) (Or.inr hdlt) (Or.inl hz0)
                  (Or.inr htlt) hlamDeg hkapDeg hmuDeg homiDeg).elim
              · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
          · rcases lt_or_eq_of_le hzle with hzlt | hzeq
            · rcases ht with ht0 | htle
              · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                  hBCDE hl0 (Or.inl hb0) (Or.inr hdlt) (Or.inr hzlt)
                  (Or.inl ht0) hlamDeg hkapDeg hmuDeg homiDeg).elim
              · rcases lt_or_eq_of_le htle with htlt | hteq
                · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                    (t := t) l alpha beta delta epsilon zeta eta theta
                    A B C D E hBCDE hl0 (Or.inl hb0) (Or.inr hdlt)
                    (Or.inr hzlt) (Or.inr htlt) hlamDeg hkapDeg hmuDeg
                    homiDeg).elim
                · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
            · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inl hzeq))⟩
        · exact Or.inr ⟨hBCDE, Or.inr (Or.inl hdeq)⟩
    · rcases lt_or_eq_of_le hble with hblt | hbeq
      · rcases hd with hd0 | hdle
        · rcases hz with hz0 | hzle
          · rcases ht with ht0 | htle
            · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                hBCDE hl0 (Or.inr hblt) (Or.inl hd0) (Or.inl hz0)
                (Or.inl ht0) hlamDeg hkapDeg hmuDeg homiDeg).elim
            · rcases lt_or_eq_of_le htle with htlt | hteq
              · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                  hBCDE hl0 (Or.inr hblt) (Or.inl hd0) (Or.inl hz0)
                  (Or.inr htlt) hlamDeg hkapDeg hmuDeg homiDeg).elim
              · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
          · rcases lt_or_eq_of_le hzle with hzlt | hzeq
            · rcases ht with ht0 | htle
              · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                  hBCDE hl0 (Or.inr hblt) (Or.inl hd0) (Or.inr hzlt)
                  (Or.inl ht0) hlamDeg hkapDeg hmuDeg homiDeg).elim
              · rcases lt_or_eq_of_le htle with htlt | hteq
                · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                    (t := t) l alpha beta delta epsilon zeta eta theta
                    A B C D E hBCDE hl0 (Or.inr hblt) (Or.inl hd0)
                    (Or.inr hzlt) (Or.inr htlt) hlamDeg hkapDeg hmuDeg
                    homiDeg).elim
                · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
            · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inl hzeq))⟩
        · rcases lt_or_eq_of_le hdle with hdlt | hdeq
          · rcases hz with hz0 | hzle
            · rcases ht with ht0 | htle
              · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                  (t := t) l alpha beta delta epsilon zeta eta theta A B C D E
                  hBCDE hl0 (Or.inr hblt) (Or.inr hdlt) (Or.inl hz0)
                  (Or.inl ht0) hlamDeg hkapDeg hmuDeg homiDeg).elim
              · rcases lt_or_eq_of_le htle with htlt | hteq
                · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                    (t := t) l alpha beta delta epsilon zeta eta theta
                    A B C D E hBCDE hl0 (Or.inr hblt) (Or.inr hdlt)
                    (Or.inl hz0) (Or.inr htlt) hlamDeg hkapDeg hmuDeg
                    homiDeg).elim
                · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
            · rcases lt_or_eq_of_le hzle with hzlt | hzeq
              · rcases ht with ht0 | htle
                · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                    (t := t) l alpha beta delta epsilon zeta eta theta
                    A B C D E hBCDE hl0 (Or.inr hblt) (Or.inr hdlt)
                    (Or.inr hzlt) (Or.inl ht0) hlamDeg hkapDeg hmuDeg
                    homiDeg).elim
                · rcases lt_or_eq_of_le htle with htlt | hteq
                  · exact (cubicLoadSigmaCone_BCDE_offWall_impossible (j := j)
                      (t := t) l alpha beta delta epsilon zeta eta theta
                      A B C D E hBCDE hl0 (Or.inr hblt) (Or.inr hdlt)
                      (Or.inr hzlt) (Or.inr htlt) hlamDeg hkapDeg hmuDeg
                      homiDeg).elim
                  · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inr hteq))⟩
              · exact Or.inr ⟨hBCDE, Or.inr (Or.inr (Or.inl hzeq))⟩
          · exact Or.inr ⟨hBCDE, Or.inr (Or.inl hdeq)⟩
      · exact Or.inr ⟨hBCDE, Or.inl hbeq⟩
  · exact Or.inl hCD

end CubicLoadMultiAssembly610

end Max11DegreeRoutes
