import Fable68LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryNextJoinScratch
import Sol68LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryReductionAssemblyScratch

/-! # Closure of the ordinary offset-120 selector

The verified offset-`120` reduction deletes its all-nonzero child and sends
the pair-zero child either to the closed offset-`240` selector or to the
ordinary all-nonzero offset-`180` face.  The latter is now empty by the
joined row-zero coefficient-`4` / I3 coefficient-`2` contradiction.  This
file only wires those source-facing packets together; it introduces no new
coefficient algebra.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryClosureAssembly68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 30000000 in
/-- The complete ordinary offset-`120` source selector is empty.  The only
packet returned by the predecessor reduction is the all-nonzero
offset-`180` face, and the imported next-join theorem closes it. -/
theorem fiveToSix_offsetOneTwenty_ordinary_source_false68
    (alpha gamma epsilon zeta eta i4 i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 2)
    (he : e.natDegree ≤ 4)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow0 : secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrow1 : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrow2 : secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    False := by
  have hreduce := fiveToSix_offsetOneTwenty_ordinary_source_reduction68
    alpha gamma epsilon zeta eta i4 i3 A B c d e hA hB hc hd he ha hb
    hi4 hi3 hrow0 hrow1 hrow2
  rcases hreduce with
    ⟨hzeta, hd1, he3, hb0, hcTop, hx, hy, hface, hdisc⟩
  have hi4z := hi4
  have hi3z := hi3
  have hrow0z := hrow0
  have hrow1z := hrow1
  rw [hzeta] at hi4z hi3z hrow0z hrow1z
  have hrow7 :
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 7 = 0 := by
    rw [hrow0z]
    simp
  have hi4rigid := fiveToSix_offsetOneEighty_nonzero_rowZero_source_packet68
    alpha gamma epsilon eta i4 A B c d e hA hB hc hd1 he3 ha hb0 hcTop
    hx hy hface hdisc hi4z hrow7
  let Cc : k[X] := (1 / 3 : k) • A ^ 2 + c
  let D0 : k[X] := (1 / 3 : k) • (A * B) + d
  let E0 : k[X] :=
    (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  have hcoords := integratedPolynomial68_cubicCoordinates
    (0 : k) alpha 0 gamma 0 epsilon 0 eta A B c D0 e
  have hhom1 : cubicHomogeneousRowOnePolynomial68 A B c D0 e =
      secondaryResidualRowOnePolynomial68 A B c d e := by
    simpa only [D0] using
      cubicHomogeneousRowOnePolynomial68_residualCoordinates A B c d e
  have hrowOneSource : lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B Cc D0 E0)
      (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B Cc D0 E0)
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
        A B Cc D0 E0) Cc D0 E0 = 0 := by
    rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
      cubicRowOnePolynomial68_split, hhom1]
    exact hrow1z
  have hrowOnePacket := fiveToSix_offsetOneEighty_nonzero_rowOne_source_packet68
    alpha gamma epsilon eta i4 i3 A B c d e hA hB hc hd1 he3 ha hb0
    hcTop hx hy hface hdisc hi4rigid hi3z
    (by simpa only [Cc, D0, E0] using hrowOneSource)
  have hedge : 9 * e.coeff 3 ^ 2 - 4 * c.coeff 2 ^ 3 = 0 :=
    hrowOnePacket.2.1
  have hrow6 :
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 6 = 0 := by
    rw [hrow0z]
    simp
  obtain ⟨hjetDisc, hjetEdge, hjetLoad⟩ :=
    fiveToSix_offsetOneEighty_ordinaryNonzeroNext_source_packet68
      alpha gamma epsilon eta i4 i3 A B c d e hA hB hc hd1 he3 ha hb0
      hcTop hx hy hface hdisc hi4rigid hi4z hi3z hrow6
  have hhom0 : cubicHomogeneousRowZeroPolynomial68 A B c D0 e =
      secondaryResidualRowZeroPolynomial68 A B c d e := by
    simpa only [D0] using
      cubicHomogeneousRowZeroPolynomial68_residualCoordinates A B c d e
  have hrowZeroSource : lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B Cc D0 E0)
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
        A B Cc D0 E0) D0 E0 = 0 := by
    rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split, hhom0]
    exact hrow0z
  have hrow5 :
      (lowerRowZeroPolynomial68
        (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B Cc D0 E0)
        (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
          A B Cc D0 E0) D0 E0).coeff 5 = 0 := by
    rw [hrowZeroSource]
    simp
  have hrow4 :
      (lowerRowZeroPolynomial68
        (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B Cc D0 E0)
        (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
          A B Cc D0 E0) D0 E0).coeff 4 = 0 := by
    rw [hrowZeroSource]
    simp
  exact fiveToSix_offsetOneEighty_ordinaryNextJoin_source_false68
    alpha gamma epsilon eta i4 i3 A B c d e hA hB hc hd1 he3 ha hb0
    hcTop hx hy hface hdisc hi4rigid hedge hjetDisc hjetEdge hjetLoad
    hi4z hi3z (by simpa only [Cc, D0, E0] using hrow5)
    (by simpa only [Cc, D0, E0] using hrow4)

#print axioms fiveToSix_offsetOneTwenty_ordinary_source_false68

end LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryClosureAssembly68

end Max11DegreeRoutes
