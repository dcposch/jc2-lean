import Sol68ScaleTwoAlignedNonsquareFixedUnifiedLoadedSquareFollowingScratch
import Fable68ScaleTwoAlignedNonsquareMixedNinthAllocationScratch

/-! # Inventory of the aligned-nonsquare quadratic-packet chamber

Untracked working note. No tracked file was edited.

Target interface: `PlaneKeller68AlignedNonsquareQuadraticPacketExclusion`,
one of the two residual scale-two hypotheses of
`Grok68ScaleTwoInterfaceCompositionScratch`.  The tracked bridge
`planeKeller68AlignedNonsquareExclusion_of_quadraticPacket` already
reduces `PlaneKeller68AlignedNonsquareExclusion` to that packet.  This
file does not claim either exclusion.

The scale-two source that feeds the packet always has `H.natDegree = 2`
(`Normalized68LeadingCoreSource P Q H 2`).  Every landed Sol68/Fable68
nonsquare constructor used below is on that degree-two chamber.

## Closed cells (cited, not re-proved)

Tracked:

* `U = D = 0` and `B = D = 0` last-row vanishings
  (`NonsquareAlignedSourceCurveData68.lastRow_U_D_ne`, `B_D_ne`).
* Polynomial-even `D = 0` and `B = 0`
  (`impossible_of_D_zero_polynomial_even`,
  `impossible_of_B_zero_polynomial_even`, and the even-cleared
  strengthenings in `monicEliminantPacket`).
* Last-row unit product and `B²` reconstruction
  (`impossible_of_unitProduct`, `impossible_of_Bsq_lastRow`).

Scratch, already consumed into the fixed-coordinate tuple:

* Same-root mixed local (`terminalLowerZero_mixedLocal_impossible_68`),
  used to force the global split `H ∣ r * phi1`.
* The `H ∣ r` leaf of that split lands inside the phi-final assembly
  (`terminalFixedRDivisorLowerZeroRefined68_phiAssembly`) and therefore
  also carries the early-geometric consumer.  It is retained as a named
  cube-loaded sibling, not deleted.

## Open cells (campaign frontier)

* Degree-two mixed square child, after the ninth-row faces already
  recorded on `terminalFixedMixedSquareNinthFaces68`.  This file
  attaches the MixedNinthAllocation transports (no new Taylor row).
* Degree-two mixed cube child `k1 = H * K` and mixed transverse child
  `D = H^2 * E2`, both still inside the loaded-next split; only the
  order-one factor transports of MixedNinthAllocation are attached.
* Early-geometric residual: no-deep-root and common-conjugate leaves
  are already consumed; component-III, `H ∣ w`, `r(a) = 0`, and the
  complete geometric selector remain opaque.
* Tracked even-cleared full divisibilities and mixed `W ≠ 0` on cores
  that have not entered the fixed-coordinate tuple.
* The named Prop `PlaneKeller68AlignedNonsquareQuadraticPacketExclusion`
  as stated (all nonsquare cores, not only degree two) remains open.

Exact gain: the mixed `B = H * B3` child of the fixed unified residual
gains the MixedNinthAllocation coordinate jets
`D''(a) = 2 H'(a) E1'(a)`, `B'''(a) = 3 H'(a) B3''(a)`, the
coordinate dichotomy `D''(a) = 0 ↔ E1'(a) = 0`, the coordinate face
`B'''(a) Φ₁(a) + 18 H'(a) w(a) D''(a) = 0`, and on the `E1'(a) = 0`
branch the unit order pin `D'''(a) ≠ 0`, the lifted `j`-face, the
transported iff `B''''(a) = 0 ↔ w(a) = 0`, and the explicit `w(a)`
root allocation, together with the peeled `E2`/`K` pins.  The cube and
transverse siblings gain only the corresponding factor transports.
No cell closes.

Next unused row: the tenth Taylor coefficient of the reduced `I₄` /
`e₁`-row on the mixed square dichotomy (MixedNinthAllocation takes no
further Taylor row), or the still-opaque component-III conjugate on
the early-geometric leaf.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000

section QuadraticPacketInventoryAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Order-one factor transports of the cube limb `k₁ = H K`. -/
def terminalFixedMixedCubeNinthAllocationFaces68
    (k1 D : k[X]) : Prop :=
  ∀ (a b : k) (K : k[X]),
    H.eval a = 0 → H.eval b = 0 →
    k1 = H * K →
    k1.derivative.eval a = H.derivative.eval a * K.eval a ∧
      k1.derivative.eval b = H.derivative.eval b * K.eval b ∧
      (D.derivative.derivative.eval a * K.eval a = 0 →
        D.derivative.derivative.eval a * k1.derivative.eval a = 0)

theorem terminalFixedMixedCubeNinthAllocationFaces_68
    (k1 D : k[X]) :
    terminalFixedMixedCubeNinthAllocationFaces68 H k1 D := by
  intro a b K ha hb hk
  have htra := productDerivativeEval_68 H K k1 a ha hk
  have htrb := productDerivativeEval_68 H K k1 b hb hk
  refine ⟨htra, htrb, ?_⟩
  intro hsplit
  linear_combination H.derivative.eval a * hsplit +
    D.derivative.derivative.eval a * htra

/-- Order-two factor transport of the transverse limb `D = H² E₂`. -/
def terminalFixedMixedTransverseNinthAllocationFaces68
    (D : k[X]) : Prop :=
  ∀ (b : k) (E2 : k[X]),
    H.eval b = 0 → D = H ^ 2 * E2 →
    D.derivative.derivative.eval b =
      2 * H.derivative.eval b ^ 2 * E2.eval b

theorem terminalFixedMixedTransverseNinthAllocationFaces_68
    (D : k[X]) :
    terminalFixedMixedTransverseNinthAllocationFaces68 H D := by
  intro b E2 hb hD
  have hmul : D = H * (H * E2) := by rw [hD]; ring
  have hm0 : (H * E2).eval b = 0 := by rw [eval_mul, hb, zero_mul]
  have hmd := productDerivativeEval_68 H E2 (H * E2) b hb rfl
  rw [productSecondDerivativeEval_68 H (H * E2) D b hb hm0 hmul, hmd]
  ring

/-- MixedNinthAllocation transports on the mixed square child, universal
in the fixed quotient witnesses.  No new Taylor row is taken. -/
def terminalFixedMixedSquareNinthAllocationFaces68
    (B D w phi1 eDot k1 : k[X]) (j : k) : Prop :=
  ∀ (a : k) (B3 E1 : k[X]),
    H.eval a = 0 → H.derivative.eval a ≠ 0 → j ≠ 0 →
    phi1.eval a ≠ 0 → k1.eval a = 0 →
    B = H * B3 → D = H * E1 →
    B3.eval a = 0 → B3.derivative.eval a = 0 → E1.eval a = 0 →
    B3 * phi1 + C 6 * H * w * E1 = 0 →
    E1 * k1 = H * B3 * w * eDot - C j * H ^ 3 →
    D.derivative.derivative.eval a =
        2 * H.derivative.eval a * E1.derivative.eval a ∧
      B.derivative.derivative.derivative.eval a =
        3 * H.derivative.eval a * B3.derivative.derivative.eval a ∧
      (D.derivative.derivative.eval a = 0 ↔
        E1.derivative.eval a = 0) ∧
      B.derivative.derivative.derivative.eval a * phi1.eval a +
          18 * H.derivative.eval a * w.eval a *
            D.derivative.derivative.eval a = 0 ∧
      ((E1.derivative.eval a = 0 ∧
          B3.derivative.derivative.eval a = 0 ∧
          k1.derivative.eval a ≠ 0 ∧
          E1.derivative.derivative.eval a ≠ 0 ∧
          E1.derivative.derivative.eval a * k1.derivative.eval a +
            2 * j * H.derivative.eval a ^ 3 = 0) →
        D.derivative.derivative.derivative.eval a =
            3 * H.derivative.eval a *
              E1.derivative.derivative.eval a ∧
          D.derivative.derivative.derivative.eval a ≠ 0 ∧
          D.derivative.derivative.derivative.eval a *
              k1.derivative.eval a +
            6 * j * H.derivative.eval a ^ 4 = 0 ∧
          B.derivative.derivative.derivative.derivative.eval a =
            4 * H.derivative.eval a *
              B3.derivative.derivative.derivative.eval a ∧
          B.derivative.derivative.derivative.derivative.eval a *
              phi1.eval a +
            24 * H.derivative.eval a * w.eval a *
              D.derivative.derivative.derivative.eval a = 0 ∧
          B.derivative.derivative.derivative.derivative.eval a *
              phi1.eval a * k1.derivative.eval a =
            144 * j * H.derivative.eval a ^ 5 * w.eval a ∧
          (B.derivative.derivative.derivative.derivative.eval a = 0 ↔
            w.eval a = 0) ∧
          ((w.eval a = 0 ∧
              B3.derivative.derivative.derivative.eval a = 0 ∧
              B.derivative.derivative.derivative.derivative.eval a
                = 0) ∨
            (w.eval a ≠ 0 ∧
              B3.derivative.derivative.derivative.eval a ≠ 0 ∧
              B.derivative.derivative.derivative.derivative.eval a
                ≠ 0)) ∧
          (∀ E2 : k[X], E1 = H * E2 →
            E2.eval a = 0 ∧
              E1.derivative.derivative.eval a =
                2 * H.derivative.eval a * E2.derivative.eval a ∧
              E2.derivative.eval a ≠ 0 ∧
              E2.derivative.eval a * k1.derivative.eval a +
                j * H.derivative.eval a ^ 2 = 0) ∧
          ∀ K : k[X], k1 = H * K →
            k1.derivative.eval a = H.derivative.eval a * K.eval a ∧
              K.eval a ≠ 0 ∧
              E1.derivative.derivative.eval a * K.eval a +
                2 * j * H.derivative.eval a ^ 2 = 0) ∧
      ((k1.derivative.eval a = 0 ∧ E1.derivative.eval a ≠ 0) →
        D.derivative.derivative.eval a ≠ 0 ∧
          (∀ E2 : k[X], E1 = H * E2 →
            E1.derivative.eval a =
                H.derivative.eval a * E2.eval a ∧
              E2.eval a ≠ 0) ∧
          ∀ K : k[X], k1 = H * K →
            K.eval a = 0 ∧
              k1.derivative.derivative.eval a =
                2 * H.derivative.eval a * K.derivative.eval a ∧
              E1.derivative.eval a *
                  (K.derivative.eval a * phi1.eval a +
                    6 * H.derivative.eval a * w.eval a ^ 2 *
                      eDot.eval a) +
                j * H.derivative.eval a ^ 2 * phi1.eval a = 0)

theorem terminalFixedMixedSquareNinthAllocationFaces_68
    (B D w phi1 eDot k1 : k[X]) (j : k) :
    terminalFixedMixedSquareNinthAllocationFaces68 H
      B D w phi1 eDot k1 j := by
  intro a B3 E1 ha hHa hj hphia hk1a hB hD hB3a hB3da hE1a
    hI4red hE1row
  have hd2ddEq :=
    productSecondDerivativeEval_68 H E1 D a ha hE1a hD
  have hb2dddEq :=
    productThirdDerivativeEval_68 H B3 B a ha hB3a hB3da hB
  have hd2ddIff : D.derivative.derivative.eval a = 0 ↔
      E1.derivative.eval a = 0 := by
    rw [hd2ddEq]
    constructor
    · intro h0
      exact (mul_eq_zero.mp h0).resolve_left
        (mul_ne_zero (by norm_num) hHa)
    · intro h0
      rw [h0, mul_zero]
  have hbracket :=
    mixedReducedIFourSecondCoefficient_68 H B3 phi1 w E1 a ha
      hB3a hB3da hE1a hI4red
  have hcoordFace :
      B.derivative.derivative.derivative.eval a * phi1.eval a +
        18 * H.derivative.eval a * w.eval a *
          D.derivative.derivative.eval a = 0 := by
    linear_combination phi1.eval a * hb2dddEq +
      18 * H.derivative.eval a * w.eval a * hd2ddEq +
      3 * H.derivative.eval a * hbracket
  refine ⟨hd2ddEq, hb2dddEq, hd2ddIff, hcoordFace, ?_, ?_⟩
  · rintro ⟨he1d, hb3dd, hk1dne, he1ddne, hpin⟩
    have htieA := mixedReducedIFourThirdCoefficientDeepZero_68 H B3
      phi1 w E1 a ha hB3a hB3da hb3dd hE1a he1d hI4red
    have helim := mixedEOneBranchPinElimination_68 hphia hj hHa hk1dne
      hpin htieA
    have hd3Eq :=
      productThirdDerivativeEval_68 H E1 D a ha hE1a he1d hD
    have hd3ne :
        D.derivative.derivative.derivative.eval a ≠ 0 := by
      rw [hd3Eq]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hHa) he1ddne
    have hd3pin :
        D.derivative.derivative.derivative.eval a *
            k1.derivative.eval a +
          6 * j * H.derivative.eval a ^ 4 = 0 := by
      linear_combination k1.derivative.eval a * hd3Eq +
        3 * H.derivative.eval a * hpin
    have hb4Eq := productFourthDerivativeEval_68 H B3 B a ha
      hB3a hB3da hb3dd hB
    have hb4face :
        B.derivative.derivative.derivative.derivative.eval a *
            phi1.eval a +
          24 * H.derivative.eval a * w.eval a *
            D.derivative.derivative.derivative.eval a = 0 := by
      linear_combination phi1.eval a * hb4Eq +
        24 * H.derivative.eval a * w.eval a * hd3Eq +
        4 * H.derivative.eval a * htieA
    have hb4jface :
        B.derivative.derivative.derivative.derivative.eval a *
            phi1.eval a * k1.derivative.eval a =
          144 * j * H.derivative.eval a ^ 5 * w.eval a := by
      linear_combination
        phi1.eval a * k1.derivative.eval a * hb4Eq +
        4 * H.derivative.eval a * helim.1
    have hb4iff :
        B.derivative.derivative.derivative.derivative.eval a = 0 ↔
          w.eval a = 0 := by
      constructor
      · intro h0
        apply helim.2.mp
        have hz : 4 * H.derivative.eval a *
            B3.derivative.derivative.derivative.eval a = 0 := by
          rw [← hb4Eq]; exact h0
        exact (mul_eq_zero.mp hz).resolve_left
          (mul_ne_zero (by norm_num) hHa)
      · intro h0
        rw [hb4Eq, helim.2.mpr h0, mul_zero]
    have halloc :
        (w.eval a = 0 ∧
            B3.derivative.derivative.derivative.eval a = 0 ∧
            B.derivative.derivative.derivative.derivative.eval a
              = 0) ∨
          (w.eval a ≠ 0 ∧
            B3.derivative.derivative.derivative.eval a ≠ 0 ∧
            B.derivative.derivative.derivative.derivative.eval a
              ≠ 0) := by
      by_cases hw : w.eval a = 0
      · exact Or.inl ⟨hw, helim.2.mpr hw, hb4iff.mpr hw⟩
      · exact Or.inr ⟨hw, fun h0 => hw (helim.2.mp h0),
          fun h0 => hw (hb4iff.mp h0)⟩
    refine ⟨hd3Eq, hd3ne, hd3pin, hb4Eq, hb4face, hb4jface, hb4iff,
      halloc, ?_, ?_⟩
    · intro E2 he2
      have he2tr := productDerivativeEval_68 H E2 E1 a ha he2
      have he2a : E2.eval a = 0 := by
        have hz : H.derivative.eval a * E2.eval a = 0 := by
          rw [← he2tr]; exact he1d
        exact (mul_eq_zero.mp hz).resolve_left hHa
      have he2Eq :=
        productSecondDerivativeEval_68 H E2 E1 a ha he2a he2
      have he2dne : E2.derivative.eval a ≠ 0 := by
        intro h0
        exact he1ddne (by rw [he2Eq, h0, mul_zero])
      have he2pin : E2.derivative.eval a * k1.derivative.eval a +
          j * H.derivative.eval a ^ 2 = 0 := by
        have hz : 2 * H.derivative.eval a *
            (E2.derivative.eval a * k1.derivative.eval a +
              j * H.derivative.eval a ^ 2) = 0 := by
          linear_combination hpin - k1.derivative.eval a * he2Eq
        exact (mul_eq_zero.mp hz).resolve_left
          (mul_ne_zero (by norm_num) hHa)
      exact ⟨he2a, he2Eq, he2dne, he2pin⟩
    · intro K hk
      have hk2tr := productDerivativeEval_68 H K k1 a ha hk
      have hk2ane : K.eval a ≠ 0 := by
        intro h0
        exact hk1dne (by rw [hk2tr, h0, mul_zero])
      have hk2pin : E1.derivative.derivative.eval a * K.eval a +
          2 * j * H.derivative.eval a ^ 2 = 0 := by
        have hz : H.derivative.eval a *
            (E1.derivative.derivative.eval a * K.eval a +
              2 * j * H.derivative.eval a ^ 2) = 0 := by
          linear_combination hpin -
            E1.derivative.derivative.eval a * hk2tr
        exact (mul_eq_zero.mp hz).resolve_left hHa
      exact ⟨hk2tr, hk2ane, hk2pin⟩
  · rintro ⟨hk1d, he1dne⟩
    have hd2ddne : D.derivative.derivative.eval a ≠ 0 := by
      rw [hd2ddEq]
      exact mul_ne_zero (mul_ne_zero (by norm_num) hHa) he1dne
    refine ⟨hd2ddne, ?_, ?_⟩
    · intro E2 he2
      have he2tr := productDerivativeEval_68 H E2 E1 a ha he2
      have he2ane : E2.eval a ≠ 0 := by
        intro h0
        exact he1dne (by rw [he2tr, h0, mul_zero])
      exact ⟨he2tr, he2ane⟩
    · intro K hk
      have hk2tr := productDerivativeEval_68 H K k1 a ha hk
      have hk2a0 : K.eval a = 0 := by
        have hz : H.derivative.eval a * K.eval a = 0 := by
          rw [← hk2tr]; exact hk1d
        exact (mul_eq_zero.mp hz).resolve_left hHa
      have hk1ddEq :=
        productSecondDerivativeEval_68 H K k1 a ha hk2a0 hk
      have hE1face := mixedEOneRowThirdCoefficient_68 H B3 w eDot E1
        k1 j a ha hB3a hB3da hE1a hk1a hE1row
      have hI4face := mixedReducedIFourSecondCoefficient_68 H B3
        phi1 w E1 a ha hB3a hB3da hE1a hI4red
      have hproduct := mixedEOneRowSecondCoefficient_68 H B3 w eDot
        E1 k1 j a ha hB3a hB3da hE1a hk1a hE1row
      have hpin2 := (mixedEOneRowAllocationSplit_68 hphia hj hHa
        hI4face hE1face hproduct).resolve_left (fun h => he1dne h.1)
      have hk2pin2 :=
        mixedNinthKTwoDeepPinTransport_68 hHa hk1ddEq hpin2.2.2
      exact ⟨hk2a0, hk1ddEq, hk2pin2⟩

end QuadraticPacketInventoryAlgebra68

section QuadraticPacketInventory68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]
  {p q : k[X][X]} {j : k}

/-- Mixed square child after the ninth-row allocation transports. -/
def terminalFixedUnifiedMixedLoadedInventory68
    (r t : k[X]) (B D w phi1 k1 : k[X]) : Prop :=
  let eDot := terminalEDerivativeNumerator68 H
    (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
      (p.coeff 3) t r)
  terminalFixedUnifiedMixedLoadedSquareFollowing68 (p := p) (j := j)
      H r t B D w phi1 k1 ∧
    terminalFixedMixedSquareNinthAllocationFaces68 H
      B D w phi1 eDot k1 j ∧
    terminalFixedMixedCubeNinthAllocationFaces68 H k1 D ∧
    terminalFixedMixedTransverseNinthAllocationFaces68 H D

/-- Degree-two quadratic-packet residual after composing the landed
fixed-unified inventory with MixedNinthAllocation.  The R-loaded and
early-geometric siblings are preserved verbatim. -/
def NonsquareAlignedQuadraticPacketInventoryResidual68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X]) : Prop :=
  terminalFixedUnifiedRLoadedConsumed68 H S r t X0 Yd B D w phi1 k1 ∨
    terminalFixedUnifiedMixedLoadedInventory68 (p := p) (j := j)
      H r t B D w phi1 k1 ∨
    terminalFixedUnifiedEarlyGeometryResidual68 H S
      r t X0 Yd B D w phi1 k1

theorem NonsquareAlignedQuadraticPacketInventoryResidual_of_squareFollowing68
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (r t X0 Yd B D w phi1 k1 : k[X])
    (h : terminalFixedUnifiedLoadedSquareFollowingResidual68 H S
      r t X0 Yd B D w phi1 k1) :
    NonsquareAlignedQuadraticPacketInventoryResidual68 H S
      r t X0 Yd B D w phi1 k1 := by
  rcases h with hR | hM | hG
  · exact Or.inl hR
  · exact Or.inr (Or.inl ⟨hM,
      terminalFixedMixedSquareNinthAllocationFaces_68 H B D w phi1
        (terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r)) k1 j,
      terminalFixedMixedCubeNinthAllocationFaces_68 H k1 D,
      terminalFixedMixedTransverseNinthAllocationFaces_68 H D⟩)
  · exact Or.inr (Or.inr hG)

/-- Same-witness source packet for the inventoried residual. -/
theorem NonsquareAlignedSourceCurveData68.quadraticPacketInventoryPacket
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ r t X0 Yd B D w phi1 k1 : k[X],
      p.coeff 4 = H * t ∧ C 3 * t - r ^ 2 = H * X0 ∧
      C 27 * p.coeff 3 - r ^ 3 = H * Yd ∧
      B * phi1 + C 6 * H * w * D = 0 ∧
      H * B * w * terminalEDerivativeNumerator68 H
          (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
            (p.coeff 3) t r) - D * k1 = C j * H ^ 4 ∧
      H ∣ r * phi1 ∧
      terminalFixedMixedLowerTransport68 H S r t X0 Yd
        B D w phi1 k1 ∧
      NonsquareAlignedQuadraticPacketInventoryResidual68 H S
        r t X0 Yd B D w phi1 k1 := by
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower, hres⟩ :=
    S.fixedUnifiedLoadedSquareFollowingPacket (H := H) hdeg hp hq
      hp6 hq8 haligned hjac hj
  exact ⟨r, t, X0, Yd, B, D, w, phi1, k1,
    hp4, hX, hY, hI4, hrow, hdvd, Tlower,
    NonsquareAlignedQuadraticPacketInventoryResidual_of_squareFollowing68
      H S r t X0 Yd B D w phi1 k1 hres⟩

end QuadraticPacketInventory68

section QuadraticPacketInventoryInterface68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Remaining hypothesis after the degree-two inventory: impossibility
of the three-way residual on a canonical same-witness tuple.  This is
strictly smaller than `PlaneKeller68AlignedNonsquareQuadraticPacketExclusion`,
which still asks for the raw packet on every nonsquare core. -/
def PlaneKeller68AlignedNonsquareQuadraticPacketInventoryExclusion
    : Prop :=
  ∀ (H : k[X]) [NonsquarePolynomial46 H] {p q : k[X][X]} {j : k}
      (S : NonsquareAlignedSourceCurveData68 H p q j)
      (r t X0 Yd B D w phi1 k1 : k[X]),
    j ≠ 0 →
    NonsquareAlignedQuadraticPacketInventoryResidual68 H S
      r t X0 Yd B D w phi1 k1 → False

/-- The aligned-nonsquare parent reduces to the inventoried residual.
The scale-two source always has `H.natDegree = 2`, so the degree-two
constructors apply.  The named packet Prop
`PlaneKeller68AlignedNonsquareQuadraticPacketExclusion` is not claimed. -/
theorem planeKeller68AlignedNonsquareExclusion_of_quadraticPacketInventory
    (hinv : PlaneKeller68AlignedNonsquareQuadraticPacketInventoryExclusion
      (k := k)) :
    PlaneKeller68AlignedNonsquareExclusion (k := k) := by
  intro P Q H hsource hnsq haligned
  letI : NonsquarePolynomial46 H := ⟨hnsq⟩
  rcases hsource with
    ⟨_hHne, hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq8' : q.coeff 8 = H ^ 4 := by simpa only [q] using hq8
  have haligned' : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0 := by
    simpa only [p, q] using haligned
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hDsrc : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [p, q, bivariateJacobian, xderiv, GCD369SourceXDeriv]
      using hjac
  obtain ⟨S⟩ := nonsquareAlignedSourceCurveData68 (H := H) p q j
    hp hq hp6' hq8' haligned' hDsrc
  obtain ⟨r, t, X0, Yd, B, D, w, phi1, k1,
      _hp4, _hX, _hY, _hI4, _hrow, _hdvd, _Tlower, hres⟩ :=
    S.quadraticPacketInventoryPacket (H := H)
      hHdegree hp hq hp6' hq8' haligned' hjac hj
  exact hinv H S r t X0 Yd B D w phi1 k1 hj hres

end QuadraticPacketInventoryInterface68

section NormalizedQuadraticPacketInventory68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

theorem normalized68ScaleTwo_alignedNonsquare_quadraticPacketInventory
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let _inst : NonsquarePolynomial46 H := ⟨hnsq⟩
    ∃ (j : k) (S : NonsquareAlignedSourceCurveData68 H p q j),
      j ≠ 0 ∧
      ∃ r t X0 Yd B D w phi1 k1 : k[X],
        p.coeff 4 = H * t ∧ C 3 * t - r ^ 2 = H * X0 ∧
        C 27 * p.coeff 3 - r ^ 3 = H * Yd ∧
        B * phi1 + C 6 * H * w * D = 0 ∧
        H * B * w * terminalEDerivativeNumerator68 H
            (cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
              (p.coeff 3) t r) - D * k1 = C j * H ^ 4 ∧
        H ∣ r * phi1 ∧
        terminalFixedMixedLowerTransport68 H S r t X0 Yd
          B D w phi1 k1 ∧
        NonsquareAlignedQuadraticPacketInventoryResidual68 H S
          r t X0 Yd B D w phi1 k1 := by
  dsimp only
  letI : NonsquarePolynomial46 H := ⟨hnsq⟩
  rcases hsource with
    ⟨_hHne, hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq8' : q.coeff 8 = H ^ 4 := by simpa only [q] using hq8
  have haligned' : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0 := by
    simpa only [p, q] using haligned
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hDsrc : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [p, q, bivariateJacobian, xderiv, GCD369SourceXDeriv]
      using hjac
  obtain ⟨S⟩ := nonsquareAlignedSourceCurveData68 (H := H) p q j
    hp hq hp6' hq8' haligned' hDsrc
  refine ⟨j, S, hj, ?_⟩
  exact S.quadraticPacketInventoryPacket (H := H)
    hHdegree hp hq hp6' hq8' haligned' hjac hj

end NormalizedQuadraticPacketInventory68

#print axioms terminalFixedMixedCubeNinthAllocationFaces_68
#print axioms terminalFixedMixedTransverseNinthAllocationFaces_68
#print axioms terminalFixedMixedSquareNinthAllocationFaces_68
#print axioms NonsquareAlignedQuadraticPacketInventoryResidual_of_squareFollowing68
#print axioms NonsquareAlignedSourceCurveData68.quadraticPacketInventoryPacket
#print axioms planeKeller68AlignedNonsquareExclusion_of_quadraticPacketInventory
#print axioms normalized68ScaleTwo_alignedNonsquare_quadraticPacketInventory

end Max11DegreeRoutes
