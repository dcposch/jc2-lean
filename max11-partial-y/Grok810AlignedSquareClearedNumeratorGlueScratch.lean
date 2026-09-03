import Grok810AlignedSquareClearedNumeratorBlocksScratch

/-! # Aligned-square cleared numerator and pole ceiling for `(8,10)` (glue)

Lanes C and T of `Grok810AlignedFaceTowerPlanScratch.md`.  Coordinator
split of `Grok810AlignedSquareClearedNumeratorRepairScratch`: the heavy
compact blocks, bar identities, block clearing, and
`alignedSquareClearedNumerator810_eq_sum_expansions` live in
`Grok810AlignedSquareClearedNumeratorBlocksScratch`.  This file holds
the source-primitive identity, RatFunc transport, scaled derivative,
and pole ceiling.  No tracked file is edited.  Bookkeeping
(`alignedSquareCompactToSourceIntegerScale810` and the grouped-scale
identity) is not repeated here.

Parents (via the Blocks module; tracked, green):

* `Grok810AlignedSquareSourceWrapperScratch`
  (`alignedSquareSourcePrimitive810`,
  `alignedSquarePrimitive810_deriv_eq_simplePole_of_source`,
  native arithmetic `119 / 0 / 119 / 119`);
* `Grok810DegreeZeroSourceNumeratorScratch`
  (`degreeZeroClearedSource810`, 25 blocks, scale `2^{62}`,
  `degreeZeroClearedSource810_map`, and the landed bar identities
  `depressedA810_eq_cleared` … `depressedW810_eq_cleared`);
* `Grok810DegreeZeroCompactBridgeScratch`
  (`rhoResidual810_eq_clearedCompact`: compact `= 2^{28} ρ`, and the
  sixteen integer-cleared identities);
* `Grok810DegreeZeroTowerOrders111to118Scratch`
  (`degreeZero_pow_dvd_of_remaining_pole810`,
  `degreeZero_of_pow_dvd_simplePole_ne_zero810`, generic in `n`).

The aligned face `λ = 0` specialises the ninth-power source numerator
without a peel.  Clearing is `7 · 17 = 119`, base order `0`, remaining
pole `119`, native ceiling `119`.  These are not the nonzero-face
Pi-tower numbers `102 / 17 / 118`.

CAS: `derive_810_aligned_square_clearing.py` (job
`20260902T132022Z-810-aligned-square-clearing-58464`).

No chamber-closure claim (lane Z follows).  No `sorry`, no new axioms,
no finite-root shortcut.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Source-level numerator at `λ = 0` -/

section AlignedSquareSourcePrimitiveIdentity810

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 800000000 in
/-- Depressed aligned coordinates are the bars over the native
denominators. -/
theorem alignedSquareSourcePrimitive810_eq_bars
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0)
    (hN : (5 : F) * a7 * h ^ 2 - (4 : F) * b9 = 0) :
    alignedSquareSourcePrimitive810 h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7
        b6 b5 b4 b3 b2 b1 =
      rhoResidual810 (0 : F)
        (alignedSquareABar810 h a7 a6 / ((16 : F) * h ^ 14))
        (alignedSquareBBar810 h a7 a6 a5 / ((32 : F) * h ^ 21))
        (alignedSquareCBar810 h a7 a6 a5 a4 / ((2048 : F) * h ^ 28))
        (alignedSquareDBar810 h a7 a6 a5 a4 a3 / ((1024 : F) * h ^ 35))
        (alignedSquareEBar810 h a7 a6 a5 a4 a3 a2 / ((65536 : F) * h ^ 42))
        (alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1 /
          ((131072 : F) * h ^ 49))
        (alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0 /
          ((16777216 : F) * h ^ 56))
        (alignedSquarePBar810 h a7 b8 / ((64 : F) * h ^ 14))
        (alignedSquareQBar810 h a7 b8 b7 / ((64 : F) * h ^ 21))
        (alignedSquareRBar810 h a7 b8 b7 b6 / ((2048 : F) * h ^ 28))
        (alignedSquareSBar810 h a7 b8 b7 b6 b5 / ((8192 : F) * h ^ 35))
        (alignedSquareTBar810 h a7 b8 b7 b6 b5 b4 /
          ((131072 : F) * h ^ 42))
        (alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3 /
          ((262144 : F) * h ^ 49))
        (alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2 /
          ((16777216 : F) * h ^ 56))
        (alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1 /
          ((67108864 : F) * h ^ 63)) := by
  have hL := alignedSquareL_eq_zero810 h a7 b9 hh hN
  have hA := alignedSquareABar810_eq h a7 a6 hh
  have hB := alignedSquareBBar810_eq h a7 a6 a5 hh
  have hC := alignedSquareCBar810_eq h a7 a6 a5 a4 hh
  have hD := alignedSquareDBar810_eq h a7 a6 a5 a4 a3 hh
  have hE := alignedSquareEBar810_eq h a7 a6 a5 a4 a3 a2 hh
  have hF := alignedSquareFBar810_eq h a7 a6 a5 a4 a3 a2 a1 hh
  have hG := alignedSquareGBar810_eq h a7 a6 a5 a4 a3 a2 a1 a0 hh
  have hP := alignedSquarePBar810_eq h a7 b9 b8 hh hN
  have hQ := alignedSquareQBar810_eq h a7 b9 b8 b7 hh hN
  have hR := alignedSquareRBar810_eq h a7 b9 b8 b7 b6 hh hN
  have hS := alignedSquareSBar810_eq h a7 b9 b8 b7 b6 b5 hh hN
  have hT := alignedSquareTBar810_eq h a7 b9 b8 b7 b6 b5 b4 hh hN
  have hU := alignedSquareUBar810_eq h a7 b9 b8 b7 b6 b5 b4 b3 hh hN
  have hV := alignedSquareVBar810_eq h a7 b9 b8 b7 b6 b5 b4 b3 b2 hh hN
  have hW :=
    alignedSquareWBar810_eq h a7 b9 b8 b7 b6 b5 b4 b3 b2 b1 hh hN
  dsimp only [alignedSquareSourcePrimitive810, sourceRhoResidual810]
  rw [hL]
  have hdiv
      {c : F} {n : ℕ} {X bar : F} (hc : c ≠ 0)
      (hn : h ^ n ≠ 0) (hid : c * h ^ n * X = bar) :
      X = bar / (c * h ^ n) :=
    (eq_div_iff (mul_ne_zero hc hn)).mpr (by
      simpa [mul_comm, mul_assoc, mul_left_comm] using hid)
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have h16777216 : (16777216 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h8192 : (8192 : F) ≠ 0 := by norm_num
  have h262144 : (262144 : F) ≠ 0 := by norm_num
  have h67108864 : (67108864 : F) ≠ 0 := by norm_num
  rw [hdiv h16 (pow_ne_zero 14 hh) hA,
    hdiv h32 (pow_ne_zero 21 hh) hB,
    hdiv h2048 (pow_ne_zero 28 hh) hC,
    hdiv h1024 (pow_ne_zero 35 hh) hD,
    hdiv h65536 (pow_ne_zero 42 hh) hE,
    hdiv h131072 (pow_ne_zero 49 hh) hF,
    hdiv h16777216 (pow_ne_zero 56 hh) hG,
    hdiv h64 (pow_ne_zero 14 hh) hP,
    hdiv h64 (pow_ne_zero 21 hh) hQ,
    hdiv h2048 (pow_ne_zero 28 hh) hR,
    hdiv h8192 (pow_ne_zero 35 hh) hS,
    hdiv h131072 (pow_ne_zero 42 hh) hT,
    hdiv h262144 (pow_ne_zero 49 hh) hU,
    hdiv h16777216 (pow_ne_zero 56 hh) hV,
    hdiv h67108864 (pow_ne_zero 63 hh) hW]

set_option maxHeartbeats 800000000 in
/-- Exact algebraic bridge from the source-level compact numerator to
the depressed primitive. -/
theorem alignedSquareClearedNumerator810_eq_scaledSourcePrimitive
    (h a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 : F)
    (hh : h ≠ 0)
    (hN : (5 : F) * a7 * h ^ 2 - (4 : F) * b9 = 0) :
    alignedSquareClearedNumerator810 h a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6
        b5 b4 b3 b2 b1 =
      (degreeZeroClearedIntegerScale810 : F) *
        h ^ alignedSquareSourceClearingPower810 *
          alignedSquareSourcePrimitive810 h a7 a6 a5 a4 a3 a2 a1 a0 b9
            b8 b7 b6 b5 b4 b3 b2 b1 := by
  let Abar := alignedSquareABar810 h a7 a6
  let Bbar := alignedSquareBBar810 h a7 a6 a5
  let Cbar := alignedSquareCBar810 h a7 a6 a5 a4
  let Dbar := alignedSquareDBar810 h a7 a6 a5 a4 a3
  let Ebar := alignedSquareEBar810 h a7 a6 a5 a4 a3 a2
  let Fbar := alignedSquareFBar810 h a7 a6 a5 a4 a3 a2 a1
  let Gbar := alignedSquareGBar810 h a7 a6 a5 a4 a3 a2 a1 a0
  let Pbar := alignedSquarePBar810 h a7 b8
  let Qbar := alignedSquareQBar810 h a7 b8 b7
  let Rbar := alignedSquareRBar810 h a7 b8 b7 b6
  let Sbar := alignedSquareSBar810 h a7 b8 b7 b6 b5
  let Tbar := alignedSquareTBar810 h a7 b8 b7 b6 b5 b4
  let Ubar := alignedSquareUBar810 h a7 b8 b7 b6 b5 b4 b3
  let Vbar := alignedSquareVBar810 h a7 b8 b7 b6 b5 b4 b3 b2
  let Wbar := alignedSquareWBar810 h a7 b8 b7 b6 b5 b4 b3 b2 b1
  have hsrc :=
    alignedSquareClearedNumerator810_eq_sum_expansions h a7 a6 a5 a4 a3
      a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1
  have hexp :=
    alignedSquareCompact_eq_sum_expansions h a7 a6 a5 a4 a3 a2 a1 a0 b8
      b7 b6 b5 b4 b3 b2 b1 hh
  have hpeel :=
    alignedSquareSourcePrimitive810_eq_bars h a7 a6 a5 a4 a3 a2 a1 a0
      b9 b8 b7 b6 b5 b4 b3 b2 b1 hh hN
  have hwt :=
    degreeZeroClearedCompact810_weightedScale h (0 : F)
      (Abar / ((16 : F) * h ^ 14)) (Bbar / ((32 : F) * h ^ 21))
      (Cbar / ((2048 : F) * h ^ 28)) (Dbar / ((1024 : F) * h ^ 35))
      (Ebar / ((65536 : F) * h ^ 42))
      (Fbar / ((131072 : F) * h ^ 49))
      (Gbar / ((16777216 : F) * h ^ 56)) (Pbar / ((64 : F) * h ^ 14))
      (Qbar / ((64 : F) * h ^ 21)) (Rbar / ((2048 : F) * h ^ 28))
      (Sbar / ((8192 : F) * h ^ 35)) (Tbar / ((131072 : F) * h ^ 42))
      (Ubar / ((262144 : F) * h ^ 49))
      (Vbar / ((16777216 : F) * h ^ 56))
      (Wbar / ((67108864 : F) * h ^ 63))
  have hL : h ^ 7 * (0 : F) = 0 := by ring
  have hA : h ^ 14 * (Abar / ((16 : F) * h ^ 14)) = Abar / 16 := by
    field_simp [hh]
  have hB : h ^ 21 * (Bbar / ((32 : F) * h ^ 21)) = Bbar / 32 := by
    field_simp [hh]
  have hC : h ^ 28 * (Cbar / ((2048 : F) * h ^ 28)) = Cbar / 2048 := by
    field_simp [hh]
  have hD : h ^ 35 * (Dbar / ((1024 : F) * h ^ 35)) = Dbar / 1024 := by
    field_simp [hh]
  have hE : h ^ 42 * (Ebar / ((65536 : F) * h ^ 42)) = Ebar / 65536 := by
    field_simp [hh]
  have hF : h ^ 49 * (Fbar / ((131072 : F) * h ^ 49)) =
      Fbar / 131072 := by
    field_simp [hh]
  have hG : h ^ 56 * (Gbar / ((16777216 : F) * h ^ 56)) =
      Gbar / 16777216 := by
    field_simp [hh]
  have hP : h ^ 14 * (Pbar / ((64 : F) * h ^ 14)) = Pbar / 64 := by
    field_simp [hh]
  have hQ : h ^ 21 * (Qbar / ((64 : F) * h ^ 21)) = Qbar / 64 := by
    field_simp [hh]
  have hR : h ^ 28 * (Rbar / ((2048 : F) * h ^ 28)) = Rbar / 2048 := by
    field_simp [hh]
  have hS : h ^ 35 * (Sbar / ((8192 : F) * h ^ 35)) = Sbar / 8192 := by
    field_simp [hh]
  have hT : h ^ 42 * (Tbar / ((131072 : F) * h ^ 42)) =
      Tbar / 131072 := by
    field_simp [hh]
  have hU : h ^ 49 * (Ubar / ((262144 : F) * h ^ 49)) =
      Ubar / 262144 := by
    field_simp [hh]
  have hV : h ^ 56 * (Vbar / ((16777216 : F) * h ^ 56)) =
      Vbar / 16777216 := by
    field_simp [hh]
  have hW : h ^ 63 * (Wbar / ((67108864 : F) * h ^ 63)) =
      Wbar / 67108864 := by
    field_simp [hh]
  have hwt' :
      degreeZeroClearedCompact810 (0 : F) (Abar / 16) (Bbar / 32)
          (Cbar / 2048) (Dbar / 1024) (Ebar / 65536) (Fbar / 131072)
          (Gbar / 16777216) (Pbar / 64) (Qbar / 64) (Rbar / 2048)
          (Sbar / 8192) (Tbar / 131072) (Ubar / 262144)
          (Vbar / 16777216) (Wbar / 67108864) =
        h ^ degreeZeroSourceClearingPower810 *
          degreeZeroClearedCompact810 (0 : F)
            (Abar / ((16 : F) * h ^ 14))
            (Bbar / ((32 : F) * h ^ 21))
            (Cbar / ((2048 : F) * h ^ 28))
            (Dbar / ((1024 : F) * h ^ 35))
            (Ebar / ((65536 : F) * h ^ 42))
            (Fbar / ((131072 : F) * h ^ 49))
            (Gbar / ((16777216 : F) * h ^ 56))
            (Pbar / ((64 : F) * h ^ 14)) (Qbar / ((64 : F) * h ^ 21))
            (Rbar / ((2048 : F) * h ^ 28))
            (Sbar / ((8192 : F) * h ^ 35))
            (Tbar / ((131072 : F) * h ^ 42))
            (Ubar / ((262144 : F) * h ^ 49))
            (Vbar / ((16777216 : F) * h ^ 56))
            (Wbar / ((67108864 : F) * h ^ 63)) := by
    rw [hL, hA, hB, hC, hD, hE, hF, hG, hP, hQ, hR, hS, hT, hU, hV, hW]
      at hwt
    exact hwt
  have hcr :=
    alignedSquareClearedCompact810_eq_scaledRho (0 : F)
      (Abar / ((16 : F) * h ^ 14)) (Bbar / ((32 : F) * h ^ 21))
      (Cbar / ((2048 : F) * h ^ 28)) (Dbar / ((1024 : F) * h ^ 35))
      (Ebar / ((65536 : F) * h ^ 42))
      (Fbar / ((131072 : F) * h ^ 49))
      (Gbar / ((16777216 : F) * h ^ 56)) (Pbar / ((64 : F) * h ^ 14))
      (Qbar / ((64 : F) * h ^ 21)) (Rbar / ((2048 : F) * h ^ 28))
      (Sbar / ((8192 : F) * h ^ 35)) (Tbar / ((131072 : F) * h ^ 42))
      (Ubar / ((262144 : F) * h ^ 49))
      (Vbar / ((16777216 : F) * h ^ 56))
      (Wbar / ((67108864 : F) * h ^ 63))
  have hextra :
      (alignedSquareCompactToSourceIntegerScale810 : F) *
          (degreeZeroGroupedIntegerScale810 : F) =
        (degreeZeroClearedIntegerScale810 : F) := by
    rw [alignedSquareClearedIntegerScale810_eq_grouped_mul, Nat.cast_mul,
      mul_comm]
  have hpow : alignedSquareSourceClearingPower810 =
      degreeZeroSourceClearingPower810 := rfl
  rw [hsrc, ← hexp, hwt', hcr, ← hpeel]
  -- Abstract the primitive so `ring` cannot unfold the residual.
  have hscale (x : F) :
      (alignedSquareCompactToSourceIntegerScale810 : F) *
          (h ^ degreeZeroSourceClearingPower810 *
            ((degreeZeroGroupedIntegerScale810 : F) * x)) =
        (degreeZeroClearedIntegerScale810 : F) *
          h ^ alignedSquareSourceClearingPower810 * x := by
    rw [hpow, ← hextra]
    ring
  exact hscale _

#print axioms alignedSquareSourcePrimitive810_eq_bars
#print axioms alignedSquareClearedNumerator810_eq_scaledSourcePrimitive

end AlignedSquareSourcePrimitiveIdentity810

section AlignedSquareClearedNumeratorRatFunc810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- Source-level identity in `k(x)`: the polynomial numerator is
`h₀^{119}` times the grouped integer scale times the depressed
primitive.  There is no `h^{102}` cancellation. -/
theorem alignedSquareClearedNumerator810_algebraMap_eq_pow_scaledPrimitive
    (h0 a7 a6 a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (hh : h0 ≠ 0)
    (hN : (5 : k[X]) * a7 * h0 ^ 2 - (4 : k[X]) * b9 = 0) :
    algebraMap k[X] (RatFunc k)
        (alignedSquareClearedNumerator810 h0 a7 a6 a5 a4 a3 a2 a1 a0 b8
          b7 b6 b5 b4 b3 b2 b1) =
      (algebraMap k[X] (RatFunc k) h0) ^
          alignedSquareSourceClearingPower810 *
        (RatFunc.C (degreeZeroClearedIntegerScale810 : k) *
          alignedSquareSourcePrimitive810
            (algebraMap k[X] (RatFunc k) h0)
            (algebraMap k[X] (RatFunc k) a7)
            (algebraMap k[X] (RatFunc k) a6)
            (algebraMap k[X] (RatFunc k) a5)
            (algebraMap k[X] (RatFunc k) a4)
            (algebraMap k[X] (RatFunc k) a3)
            (algebraMap k[X] (RatFunc k) a2)
            (algebraMap k[X] (RatFunc k) a1)
            (algebraMap k[X] (RatFunc k) a0)
            (algebraMap k[X] (RatFunc k) b9)
            (algebraMap k[X] (RatFunc k) b8)
            (algebraMap k[X] (RatFunc k) b7)
            (algebraMap k[X] (RatFunc k) b6)
            (algebraMap k[X] (RatFunc k) b5)
            (algebraMap k[X] (RatFunc k) b4)
            (algebraMap k[X] (RatFunc k) b3)
            (algebraMap k[X] (RatFunc k) b2)
            (algebraMap k[X] (RatFunc k) b1)) := by
  let φ : k[X] →+* RatFunc k := algebraMap k[X] (RatFunc k)
  have hhRF : φ h0 ≠ 0 := RatFunc.algebraMap_ne_zero hh
  have hNrat :
      (5 : RatFunc k) * φ a7 * φ h0 ^ 2 - (4 : RatFunc k) * φ b9 = 0 := by
    have hmapped := congrArg φ hN
    simpa [φ, map_sub, map_mul, map_pow, map_ofNat] using hmapped
  have hmap :=
    alignedSquareClearedNumerator810_map φ h0 a7 a6 a5 a4 a3 a2 a1 a0 b8
      b7 b6 b5 b4 b3 b2 b1
  have hfield :=
    alignedSquareClearedNumerator810_eq_scaledSourcePrimitive (φ h0)
      (φ a7) (φ a6) (φ a5) (φ a4) (φ a3) (φ a2) (φ a1) (φ a0) (φ b9)
      (φ b8) (φ b7) (φ b6) (φ b5) (φ b4) (φ b3) (φ b2) (φ b1) hhRF hNrat
  have hscale : (degreeZeroClearedIntegerScale810 : RatFunc k) =
      RatFunc.C (degreeZeroClearedIntegerScale810 : k) :=
    (map_natCast (RatFunc.C : k →+* RatFunc k)
      degreeZeroClearedIntegerScale810).symm
  rw [hmap, hfield]
  simp only [φ, alignedSquareSourceClearingPower810]
  rw [hscale]
  ring

#print axioms alignedSquareClearedNumerator810_algebraMap_eq_pow_scaledPrimitive

end AlignedSquareClearedNumeratorRatFunc810

/-! ## Scaled simple pole `deriv (2^{62} ρ) = C(2^{62} j) / h₀` -/

section AlignedSquareScaledDeriv810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 800000000 in
/-- The scaled aligned-square primitive has the ordinary simple-pole
derivative supplied by the affine source Jacobian.  The residue is
`2^{62} j`. -/
theorem alignedSquarePrimitive810_scaledDeriv_eq_simplePole_of_source
    (p q : k[X][X]) (H h0 : k[X]) (j : k)
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (haligned :
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    Differential.deriv
        ((degreeZeroClearedIntegerScale810 : RatFunc k) *
          alignedSquareSourcePrimitive810
            (algebraMap k[X] (RatFunc k) h0)
            (algebraMap k[X] (RatFunc k) (p.coeff 7))
            (algebraMap k[X] (RatFunc k) (p.coeff 6))
            (algebraMap k[X] (RatFunc k) (p.coeff 5))
            (algebraMap k[X] (RatFunc k) (p.coeff 4))
            (algebraMap k[X] (RatFunc k) (p.coeff 3))
            (algebraMap k[X] (RatFunc k) (p.coeff 2))
            (algebraMap k[X] (RatFunc k) (p.coeff 1))
            (algebraMap k[X] (RatFunc k) (p.coeff 0))
            (algebraMap k[X] (RatFunc k) (q.coeff 9))
            (algebraMap k[X] (RatFunc k) (q.coeff 8))
            (algebraMap k[X] (RatFunc k) (q.coeff 7))
            (algebraMap k[X] (RatFunc k) (q.coeff 6))
            (algebraMap k[X] (RatFunc k) (q.coeff 5))
            (algebraMap k[X] (RatFunc k) (q.coeff 4))
            (algebraMap k[X] (RatFunc k) (q.coeff 3))
            (algebraMap k[X] (RatFunc k) (q.coeff 2))
            (algebraMap k[X] (RatFunc k) (q.coeff 1))) =
      RatFunc.C ((degreeZeroClearedIntegerScale810 : k) * j) /
        algebraMap k[X] (RatFunc k) h0 := by
  let phi : k[X] →+* RatFunc k := algebraMap k[X] (RatFunc k)
  have hprim :=
    alignedSquarePrimitive810_deriv_eq_simplePole_of_source p q H h0 j
      hp hq hh0 hH hp8 hq10 haligned hD
  have hnum : (degreeZeroClearedIntegerScale810 : RatFunc k) =
      RatFunc.C (degreeZeroClearedIntegerScale810 : k) :=
    (map_natCast (RatFunc.C : k →+* RatFunc k)
      degreeZeroClearedIntegerScale810).symm
  let prim : RatFunc k :=
    alignedSquareSourcePrimitive810 (phi h0) (phi (p.coeff 7))
      (phi (p.coeff 6)) (phi (p.coeff 5)) (phi (p.coeff 4))
      (phi (p.coeff 3)) (phi (p.coeff 2)) (phi (p.coeff 1))
      (phi (p.coeff 0)) (phi (q.coeff 9)) (phi (q.coeff 8))
      (phi (q.coeff 7)) (phi (q.coeff 6)) (phi (q.coeff 5))
      (phi (q.coeff 4)) (phi (q.coeff 3)) (phi (q.coeff 2))
      (phi (q.coeff 1))
  have hleib :
      Differential.deriv
          ((degreeZeroClearedIntegerScale810 : RatFunc k) * prim) =
        (degreeZeroClearedIntegerScale810 : RatFunc k) *
          (RatFunc.C j / phi h0) := by
    have hmul :
        Differential.deriv
            (RatFunc.C (degreeZeroClearedIntegerScale810 : k) * prim) =
          RatFunc.C (degreeZeroClearedIntegerScale810 : k) *
            Differential.deriv prim := by
      simpa [ratFuncDerivation46_apply, Algebra.smul_def] using
        ratFuncDerivation46.map_smul
          (degreeZeroClearedIntegerScale810 : k) prim
    rw [hnum, hmul]
    dsimp [prim, phi]
    rw [hprim]
  have hscale :
      (degreeZeroClearedIntegerScale810 : RatFunc k) *
          (RatFunc.C j / phi h0) =
        RatFunc.C ((degreeZeroClearedIntegerScale810 : k) * j) /
          phi h0 := by
    rw [hnum, div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, ← map_mul]
  rw [hleib, hscale]

#print axioms alignedSquarePrimitive810_scaledDeriv_eq_simplePole_of_source

end AlignedSquareScaledDeriv810

/-! ## Lane T: remaining pole `119` and native ceiling -/

section AlignedSquarePoleCeiling810

variable {k : Type*} [Field k] [CharZero k]

/-- The compact numerator, as a pole-`119` numerator of a simple-pole
rational function, is divisible by `h₀^{119}`. -/
theorem alignedSquareClearedNumerator810_pow_oneHundredNineteen_dvd
    (h0 a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareClearedNumerator810 h0 a7 a6 a5 a4 a3 a2 a1 a0
            b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^
            alignedSquareRemainingPole810 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ alignedSquareTowerCeiling810 ∣
      alignedSquareClearedNumerator810 h0 a7 a6 a5 a4 a3 a2 a1 a0 b8 b7
        b6 b5 b4 b3 b2 b1 := by
  simpa [alignedSquareTowerCeiling810, alignedSquareRemainingPole810]
    using
    degreeZero_pow_dvd_of_remaining_pole810 h0
      (alignedSquareClearedNumerator810 h0 a7 a6 a5 a4 a3 a2 a1 a0 b8
        b7 b6 b5 b4 b3 b2 b1)
      rho j a 119 hh0 hdegree hroot hclear hderiv

#print axioms alignedSquareClearedNumerator810_pow_oneHundredNineteen_dvd

/-- Source-facing joint order-`119` packet of the aligned-square
`(8,10)` compact numerator.  After `h₀^{119}` the remaining factor is
`rho`; `j ≠ 0` is impossible.  The chamber is not closed on the raw
source hypotheses. -/
theorem alignedSquareFace810_order119Ceiling
    (h0 a7 a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : k[X])
    (rho : RatFunc k) (j a : k) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (alignedSquareClearedNumerator810 h0 a7 a6 a5 a4 a3 a2 a1 a0
            b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^
            alignedSquareRemainingPole810 *
          rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  obtain ⟨Q, hQ⟩ :=
    alignedSquareClearedNumerator810_pow_oneHundredNineteen_dvd h0 a7
      a6 a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 rho j a hh0 hdegree
      hroot hclear hderiv
  have hclear119 :
      algebraMap k[X] (RatFunc k)
          (alignedSquareClearedNumerator810 h0 a7 a6 a5 a4 a3 a2 a1 a0
            b8 b7 b6 b5 b4 b3 b2 b1) =
        (algebraMap k[X] (RatFunc k) h0) ^ 119 * rho := by
    simpa [alignedSquareRemainingPole810] using hclear
  exact degreeZero_of_pow_dvd_simplePole_ne_zero810 a j h0
    (alignedSquareClearedNumerator810 h0 a7 a6 a5 a4 a3 a2 a1 a0 b8 b7
      b6 b5 b4 b3 b2 b1)
    Q rho 119 hh0 hroot hQ hclear119 hderiv hj

#print axioms alignedSquareFace810_order119Ceiling

end AlignedSquarePoleCeiling810

end Max11DegreeRoutes
