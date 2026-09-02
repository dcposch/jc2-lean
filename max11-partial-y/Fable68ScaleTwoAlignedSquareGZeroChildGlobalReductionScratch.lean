import Fable68ScaleTwoAlignedSquareGZeroChildEighthScratch

/-! # The global reduction of the `G[-1] = 0` children

The eighth residual keeps the `G[-1] = 0` sibling as the refined
disjunction `BGainRefinedEighth ∨ FGainRefinedEighth`, with the
coefficient-nine `I₄` row and the coefficient-seven `I₃` row unused.
This file deliberately takes *no* further Taylor rows.  Instead the
whole remaining row tower is replaced by a single global reduction of
the two exact factored first integrals, carried out at the `RatFunc`
level and then cleared to polynomial identities:

* the exact `firstIntegralFour` load factor
  `rhoOneGZeroChildI4LoadFactored68`:
  `(-8/27)B³ + (8/3)BG + (4/3)(2C+3γ)F + 2εB = i₄`,
* the exact `firstIntegralThree` cap factor `rhoOneI3CapFactored68`:
  `(-8/9)ABF - (8/9)B²C + (4/3)(2C+3γ)G + (4/3)F² - (2/3)γB² + 2εC = i₃`,
* the finite `A`-support statement in its exact global form: the source
  coordinate `A` clears to the polynomial `u - (5/12)g²` against `h₀²`
  (`clearedCoordinatesRhoOne`); the eighth file's coefficient ceiling
  `A[m] = 0` for `deg(u - (5/12)g²) < m + 2` is precisely the jet
  shadow of this clearing, and here the clearing itself is consumed,
* the accumulated `γ`-loaded minor, globalized: the per-coefficient
  minors of the fourth through eighth files eliminated the `G`-jet row
  by row with multipliers built from `B[2]`-powers and `C`-defects; the
  global multiplier pair `(54B, -27(2C+3γ))` eliminates the *entire*
  `G` coordinate in one identity
  (`rhoOneGZeroChildGlobalMinorFactored68`):
  `54B·i₃ - 27(2C+3γ)·i₄ =
     -48AB²F - 32B³C - 36(2C+3γ)²F + 72BF² - 12γB³ - 162γεB`,
  which stays `γ`-loaded through the `B³` block and ground-loaded
  through the single `γεB` term, exactly as every accumulated minor
  was `γ`-loaded through its `B²` boundary.

Clearing the minor and both factors against the scale (`A ~ h₀⁻²`,
`B ~ h₀⁻³`, tangent `C ~ h₀⁻⁴`, `F ~ h₀⁻⁵`, `G ~ h₀⁻⁶`; every exponent
supplied by `clearedCoordinatesRhoOne`, no `X`-degree bound anywhere)
gives the cleared-polynomial packet `RhoOneGZeroChildGlobalCleared68`
in `k[X]`: with `A₁ = u - (5/12)g²`, `B₁`, tangent numerators
`C₂ = C₁ - (1/3)A₁²`, `F₂ = D₁ - (1/3)A₁B₁`,
`G₂ = E₁ - (1/27)A₁³ - (1/3)A₁C₂` and `S₂ = 2C₂ + 3γh₀⁴`,

* `72B₁G₂ - 8B₁³ + 36S₂F₂ + 54εB₁h₀⁶ = 27i₄h₀⁹`,
* `12S₂G₂ - 8A₁B₁F₂ - 8B₁²C₂ + 12F₂² - 6γB₁²h₀⁴ + 18εC₂h₀⁶ = 9i₃h₀¹⁰`,
* `54B₁i₃h₀¹⁰ - 27S₂i₄h₀⁹ =
     -48A₁B₁²F₂ - 32B₁³C₂ - 36S₂²F₂ + 72B₁F₂² - 12γB₁³h₀⁴ - 162γεB₁h₀¹⁰`.

Every Taylor row the tower could still take is a Hahn-coefficient
shadow of the first two identities, and every `G`-eliminated minor the
tower could still accumulate is a shadow of the third; the tower is
replaced, not truncated.

The sought factor/divisibility/order contradiction does *not* exist at
this level: the identities force the exact scale-adic order gains
`h₀⁴ ∣ 48A₁B₁²F₂ + 32B₁³C₂ + 36S₂²F₂ - 72B₁F₂²` and
`h₀⁹ ∣ 48A₁B₁²F₂ + 32B₁³C₂ + 36S₂²F₂ - 72B₁F₂² + 12γB₁³h₀⁴`
(`rhoOne_gZeroChildGlobal_scaleDivisibility`) together with the
`γ`-, `ε`- and integral-free root tie
`6A₁(a)B₁(a)²F₂(a) + 4B₁(a)³C₂(a) + 18C₂(a)²F₂(a) = 9B₁(a)F₂(a)²`
(`rhoOne_gZeroChildGlobal_rootTie`), but the cubic-core one-parameter
family (`rhoOne_cubicCore_branch_all_topRows_zero`) kills every one of
these constraints — `A₁`, `B₁`, `C₂`, `F₂` and `G₂` all vanish
identically on it — so no contradiction is derivable from the two
polynomial first integrals alone, with or without an `X`-degree bound.
The exact finite source-facing global residual is therefore returned:
`rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenGlobalReductionResidual`
conjoins the cleared global packet with the eighth residual kept
verbatim — the nonzero `G[-1]` boundary lane, the `C₂` face, the
quadratic rays and both refined children are all preserved literally.
NEXT_UNUSED_ROW: unchanged — the coefficient-nine `I₄` row and the
coefficient-seven `I₃` row on both children (deliberately not taken;
their content is the `9`-th and `7`-th Hahn shadows of the cleared
global identities above). -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareGZeroChildGlobalReduction68

variable {k : Type*} [Field k] [CharZero k]

/-- The global `G`-eliminated minor of the two exact factored first
integrals: multiplying the `I₃` cap factor by `54B` and the `I₄` load
factor by `27(2C+3γ)` cancels the whole `G` coordinate — not one jet
coefficient at a time, as the accumulated `γ`-loaded minors of the
fourth through eighth files did, but globally.  The result stays
`γ`-loaded through the `B³` block and ground-loaded through the single
`162γεB` term, and is otherwise built from the `ABF`, `B³C`, `S²F` and
`BF²` blocks alone. -/
theorem rhoOneGZeroChildGlobalMinorFactored68
    (gamma epsilon i4 i3 A B C F G : k)
    (hi4 : rhoOneGZeroChildI4LoadFactored68 gamma epsilon B C F G = i4)
    (hi3 : rhoOneI3CapFactored68 gamma epsilon A B C F G = i3) :
    54 * B * i3 - 27 * (2 * C + 3 * gamma) * i4 =
      -48 * A * B ^ 2 * F - 32 * B ^ 3 * C -
        36 * (2 * C + 3 * gamma) ^ 2 * F + 72 * B * F ^ 2 -
        12 * gamma * B ^ 3 - 162 * gamma * epsilon * B := by
  simp only [rhoOneGZeroChildI4LoadFactored68, rhoOneI3CapFactored68]
    at hi4 hi3
  linear_combination (-54 * B : k) * hi3 +
    (27 * (2 * C + 3 * gamma) : k) * hi4

/-- The cleared main-tangent `C`-numerator: `h₀⁴` times the tangent
coordinate `C = C₀ - (1/3)A²`. -/
def gZeroGlobalTangentC68 (h0 g u a3 a2 : k[X]) : k[X] :=
  localClearedC68RhoOne h0 g u a3 a2 -
    C (1 / 3 : k) * localClearedA68RhoOne g u ^ 2

/-- The cleared main-tangent `F`-numerator: `h₀⁵` times the tangent
coordinate `F = D - (1/3)AB`. -/
def gZeroGlobalTangentF68 (h0 g u a3 a2 a1 : k[X]) : k[X] :=
  localClearedD68RhoOne h0 g u a3 a2 a1 -
    C (1 / 3 : k) * localClearedA68RhoOne g u *
      localClearedB68RhoOne g u a3

/-- The cleared main-tangent `G`-numerator: `h₀⁶` times the tangent
coordinate `G = E - (1/27)A³ - (1/3)AC`. -/
def gZeroGlobalTangentG68 (h0 g u a3 a2 a1 a0 : k[X]) : k[X] :=
  localClearedE68RhoOne h0 g u a3 a2 a1 a0 -
    C (1 / 27 : k) * localClearedA68RhoOne g u ^ 3 -
    C (1 / 3 : k) * localClearedA68RhoOne g u *
      gZeroGlobalTangentC68 h0 g u a3 a2

/-- The exact clearings of the three main-tangent coordinates against
the scale, inherited from the five source clearings — this is the
global form of the finite `A`-support statement: each tangent
coordinate is a polynomial divided by an explicit `h₀`-power, with no
bound on the `X`-degree of the numerator. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_gZeroGlobal_clearedTangentCoordinates
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u) :
    algebraMap k[X] (RatFunc k)
        (gZeroGlobalTangentC68 h0 g u (p.coeff 3) (p.coeff 2)) =
      algebraMap k[X] (RatFunc k) h0 ^ 4 *
        (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2) ∧
    algebraMap k[X] (RatFunc k)
        (gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1)) =
      algebraMap k[X] (RatFunc k) h0 ^ 5 *
        (T.source.D - RatFunc.C (1 / 3 : k) * T.source.A * T.source.B) ∧
    algebraMap k[X] (RatFunc k)
        (gZeroGlobalTangentG68 h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0)) =
      algebraMap k[X] (RatFunc k) h0 ^ 6 *
        ((T.source.E - RatFunc.C (1 / 27 : k) * T.source.A ^ 3) -
          RatFunc.C (1 / 3 : k) * T.source.A *
            (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2)) := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := T.source.clearedCoordinatesRhoOne
    hp T.scale_ne_zero hH hp6 hp5 hp4
  refine ⟨?_, ?_, ?_⟩
  · simp only [gZeroGlobalTangentC68, map_sub, map_mul, map_pow,
      RatFunc.algebraMap_C]
    rw [hC, hA]
    ring
  · simp only [gZeroGlobalTangentF68, map_sub, map_mul, map_pow,
      RatFunc.algebraMap_C]
    rw [hD, hA, hB]
    ring
  · simp only [gZeroGlobalTangentG68, gZeroGlobalTangentC68, map_sub,
      map_mul, map_pow, RatFunc.algebraMap_C]
    rw [hE, hA, hC]
    ring

/-- The cleared-polynomial global reduction of the `G[-1] = 0`
children: the `I₄` load factor cleared at `h₀⁹`, the `I₃` cap factor
cleared at `h₀¹⁰`, and the `G`-jet-free global minor cleared at
`h₀¹³`.  All three are identities in `k[X]`, valid with unbounded
`X`-degree; every coefficient row of the remaining tower is a Hahn
shadow of the first two, and every accumulated `γ`-loaded minor is a
shadow of the third. -/
def RhoOneGZeroChildGlobalCleared68
    (gamma epsilon i4 i3 : k) (h0 A1 B1 C2 F2 G2 : k[X]) : Prop :=
  72 * B1 * G2 - 8 * B1 ^ 3 +
      36 * (2 * C2 + 3 * C gamma * h0 ^ 4) * F2 +
      54 * C epsilon * B1 * h0 ^ 6 =
    27 * C i4 * h0 ^ 9 ∧
  12 * (2 * C2 + 3 * C gamma * h0 ^ 4) * G2 - 8 * A1 * B1 * F2 -
      8 * B1 ^ 2 * C2 + 12 * F2 ^ 2 - 6 * C gamma * B1 ^ 2 * h0 ^ 4 +
      18 * C epsilon * C2 * h0 ^ 6 =
    9 * C i3 * h0 ^ 10 ∧
  54 * B1 * C i3 * h0 ^ 10 -
      27 * (2 * C2 + 3 * C gamma * h0 ^ 4) * C i4 * h0 ^ 9 =
    -48 * A1 * B1 ^ 2 * F2 - 32 * B1 ^ 3 * C2 -
      36 * (2 * C2 + 3 * C gamma * h0 ^ 4) ^ 2 * F2 +
      72 * B1 * F2 ^ 2 - 12 * C gamma * B1 ^ 3 * h0 ^ 4 -
      162 * C gamma * C epsilon * B1 * h0 ^ 10

set_option maxHeartbeats 1600000 in
/-- The global cleared reduction holds on the whole aligned-square
`ρ = 1` source with `β = δ = ζ = 0` — no child box, no order bound and
no `X`-degree bound is needed.  The two integral scalars are produced
by the ground bracket exactly as in the row tower, the factored forms
are the exact `firstIntegralFour` load factor and `firstIntegralThree`
cap factor, and the clearing exponents are those of the finite
`A`-support statement. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_gZeroChildGlobalClearedReduction
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    ∃ i4 i3 : k,
      RhoOneGZeroChildGlobalCleared68 T.source.gamma T.source.epsilon
        i4 i3 h0 (localClearedA68RhoOne g u)
        (localClearedB68RhoOne g u (p.coeff 3))
        (gZeroGlobalTangentC68 h0 g u (p.coeff 3) (p.coeff 2))
        (gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1))
        (gZeroGlobalTangentG68 h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0)) := by
  obtain ⟨i4, i3, hi4raw, hi3raw⟩ :=
    integratedFirstIntegrals_exist_ground68
      T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  rw [hbeta, hdelta, hzeta] at hi4raw hi3raw
  have hCrec : T.source.A ^ 2 / 3 +
      (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2) =
        T.source.C0 := by
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hDrec : T.source.A * T.source.B / 3 +
      (T.source.D - RatFunc.C (1 / 3 : k) * T.source.A * T.source.B) =
        T.source.D := by
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hErec : T.source.A ^ 3 / 27 +
      T.source.A *
        (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2) / 3 +
      ((T.source.E - RatFunc.C (1 / 27 : k) * T.source.A ^ 3) -
        RatFunc.C (1 / 3 : k) * T.source.A *
          (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2)) =
        T.source.E := by
    simp only [RatFunc.algebraMap_eq_C, map_div₀, map_one, map_ofNat]
    ring
  have hi4T : firstIntegralFour68 0 T.source.A T.source.B
      (T.source.A ^ 2 / 3 +
        (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2))
      (T.source.A * T.source.B / 3 +
        (T.source.D - RatFunc.C (1 / 3 : k) * T.source.A * T.source.B))
      (T.source.A ^ 3 / 27 +
        T.source.A *
          (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2) / 3 +
        ((T.source.E - RatFunc.C (1 / 27 : k) * T.source.A ^ 3) -
          RatFunc.C (1 / 3 : k) * T.source.A *
            (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2)))
      0 (RatFunc.C T.source.gamma) 0 (RatFunc.C T.source.epsilon) 0 =
        RatFunc.C i4 := by
    rw [hCrec, hDrec, hErec]
    simpa only [RatFunc.algebraMap_eq_C, map_zero] using hi4raw
  have hi3T : firstIntegralThree68 0 T.source.A T.source.B
      (T.source.A ^ 2 / 3 +
        (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2))
      (T.source.A * T.source.B / 3 +
        (T.source.D - RatFunc.C (1 / 3 : k) * T.source.A * T.source.B))
      (T.source.A ^ 3 / 27 +
        T.source.A *
          (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2) / 3 +
        ((T.source.E - RatFunc.C (1 / 27 : k) * T.source.A ^ 3) -
          RatFunc.C (1 / 3 : k) * T.source.A *
            (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2)))
      0 (RatFunc.C T.source.gamma) 0 (RatFunc.C T.source.epsilon) 0 =
        RatFunc.C i3 := by
    rw [hCrec, hDrec, hErec]
    simpa only [RatFunc.algebraMap_eq_C, map_zero] using hi3raw
  have hload := firstIntegralFour_gZeroChild_load_factor68
    (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
    T.source.A T.source.B
    (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2)
    (T.source.D - RatFunc.C (1 / 3 : k) * T.source.A * T.source.B)
    ((T.source.E - RatFunc.C (1 / 27 : k) * T.source.A ^ 3) -
      RatFunc.C (1 / 3 : k) * T.source.A *
        (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2))
    (RatFunc.C i4) hi4T
  have hcap := firstIntegralThree_cap_factor68
    (RatFunc.C T.source.gamma) (RatFunc.C T.source.epsilon)
    T.source.A T.source.B
    (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2)
    (T.source.D - RatFunc.C (1 / 3 : k) * T.source.A * T.source.B)
    ((T.source.E - RatFunc.C (1 / 27 : k) * T.source.A ^ 3) -
      RatFunc.C (1 / 3 : k) * T.source.A *
        (T.source.C0 - RatFunc.C (1 / 3 : k) * T.source.A ^ 2))
    (RatFunc.C i3) hi3T
  simp only [rhoOneGZeroChildI4LoadFactored68] at hload
  simp only [rhoOneI3CapFactored68] at hcap
  obtain ⟨hA, hB, -, -, -⟩ := T.source.clearedCoordinatesRhoOne
    hp T.scale_ne_zero hH hp6 hp5 hp4
  obtain ⟨hCt, hFt, hGt⟩ :=
    T.rhoOne_gZeroGlobal_clearedTangentCoordinates hp hH hp6 hp5 hp4
  have hI4c : 72 * localClearedB68RhoOne g u (p.coeff 3) *
        gZeroGlobalTangentG68 h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0) -
      8 * localClearedB68RhoOne g u (p.coeff 3) ^ 3 +
      36 * (2 * gZeroGlobalTangentC68 h0 g u (p.coeff 3) (p.coeff 2) +
          3 * C T.source.gamma * h0 ^ 4) *
        gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1) +
      54 * C T.source.epsilon * localClearedB68RhoOne g u (p.coeff 3) *
        h0 ^ 6 =
      27 * C i4 * h0 ^ 9 := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
      RatFunc.algebraMap_C]
    rw [hB, hCt, hFt, hGt]
    linear_combination (27 : RatFunc k) *
      algebraMap k[X] (RatFunc k) h0 ^ 9 * hload
  have hI3c : 12 * (2 * gZeroGlobalTangentC68 h0 g u (p.coeff 3)
          (p.coeff 2) +
        3 * C T.source.gamma * h0 ^ 4) *
        gZeroGlobalTangentG68 h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0) -
      8 * localClearedA68RhoOne g u *
        localClearedB68RhoOne g u (p.coeff 3) *
        gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1) -
      8 * localClearedB68RhoOne g u (p.coeff 3) ^ 2 *
        gZeroGlobalTangentC68 h0 g u (p.coeff 3) (p.coeff 2) +
      12 * gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1) ^ 2 -
      6 * C T.source.gamma * localClearedB68RhoOne g u (p.coeff 3) ^ 2 *
        h0 ^ 4 +
      18 * C T.source.epsilon *
        gZeroGlobalTangentC68 h0 g u (p.coeff 3) (p.coeff 2) * h0 ^ 6 =
      9 * C i3 * h0 ^ 10 := by
    apply FaithfulSMul.algebraMap_injective k[X] (RatFunc k)
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
      RatFunc.algebraMap_C]
    rw [hA, hB, hCt, hFt, hGt]
    linear_combination (9 : RatFunc k) *
      algebraMap k[X] (RatFunc k) h0 ^ 10 * hcap
  refine ⟨i4, i3, ?_⟩
  dsimp only [RhoOneGZeroChildGlobalCleared68]
  refine ⟨hI4c, hI3c, ?_⟩
  linear_combination (2 * gZeroGlobalTangentC68 h0 g u (p.coeff 3)
        (p.coeff 2) +
      3 * C T.source.gamma * h0 ^ 4 : k[X]) * hI4c -
    (6 * localClearedB68RhoOne g u (p.coeff 3) : k[X]) * hI3c

set_option maxHeartbeats 800000 in
/-- The exact scale-adic order gains of the global reduction: the
`G`-free minor combination gains four `h₀`-orders outright and nine
once the `γ`-load is carried along — a divisibility valid with
unbounded `X`-degree, packaging at once every root-order condition the
consumed and unconsumed minor rows could supply. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_gZeroChildGlobal_scaleDivisibility
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    h0 ^ 4 ∣
      48 * localClearedA68RhoOne g u *
          localClearedB68RhoOne g u (p.coeff 3) ^ 2 *
          gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
            (p.coeff 1) +
        32 * localClearedB68RhoOne g u (p.coeff 3) ^ 3 *
          gZeroGlobalTangentC68 h0 g u (p.coeff 3) (p.coeff 2) +
        36 * (2 * gZeroGlobalTangentC68 h0 g u (p.coeff 3) (p.coeff 2) +
            3 * C T.source.gamma * h0 ^ 4) ^ 2 *
          gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
            (p.coeff 1) -
        72 * localClearedB68RhoOne g u (p.coeff 3) *
          gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
            (p.coeff 1) ^ 2 ∧
    h0 ^ 9 ∣
      48 * localClearedA68RhoOne g u *
          localClearedB68RhoOne g u (p.coeff 3) ^ 2 *
          gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
            (p.coeff 1) +
        32 * localClearedB68RhoOne g u (p.coeff 3) ^ 3 *
          gZeroGlobalTangentC68 h0 g u (p.coeff 3) (p.coeff 2) +
        36 * (2 * gZeroGlobalTangentC68 h0 g u (p.coeff 3) (p.coeff 2) +
            3 * C T.source.gamma * h0 ^ 4) ^ 2 *
          gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
            (p.coeff 1) -
        72 * localClearedB68RhoOne g u (p.coeff 3) *
          gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
            (p.coeff 1) ^ 2 +
        12 * C T.source.gamma *
          localClearedB68RhoOne g u (p.coeff 3) ^ 3 * h0 ^ 4 := by
  obtain ⟨i4, i3, hpack⟩ := T.rhoOne_gZeroChildGlobalClearedReduction
    hp hH hp6 hp5 hp4 hbeta hdelta hzeta
  dsimp only [RhoOneGZeroChildGlobalCleared68] at hpack
  obtain ⟨-, -, h3⟩ := hpack
  constructor
  · refine ⟨-54 * localClearedB68RhoOne g u (p.coeff 3) * C i3 *
        h0 ^ 6 +
      27 * (2 * gZeroGlobalTangentC68 h0 g u (p.coeff 3) (p.coeff 2) +
          3 * C T.source.gamma * h0 ^ 4) * C i4 * h0 ^ 5 -
      12 * C T.source.gamma *
        localClearedB68RhoOne g u (p.coeff 3) ^ 3 -
      162 * C T.source.gamma * C T.source.epsilon *
        localClearedB68RhoOne g u (p.coeff 3) * h0 ^ 6, ?_⟩
    linear_combination h3
  · refine ⟨-54 * localClearedB68RhoOne g u (p.coeff 3) * C i3 * h0 +
      27 * (2 * gZeroGlobalTangentC68 h0 g u (p.coeff 3) (p.coeff 2) +
          3 * C T.source.gamma * h0 ^ 4) * C i4 -
      162 * C T.source.gamma * C T.source.epsilon *
        localClearedB68RhoOne g u (p.coeff 3) * h0, ?_⟩
    linear_combination h3

/-- The finite source-facing root tie of the global reduction: at the
selected root the cleared minor loses every `h₀`-loaded term — the
integral scalars, `γ` and `ε` all leave — and what remains is a single
scalar relation among the evaluated cleared tangent coordinates.  This
is the residual the replaced tower faces at the source. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_gZeroChildGlobal_rootTie
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    6 * (localClearedA68RhoOne g u).eval T.root *
        (localClearedB68RhoOne g u (p.coeff 3)).eval T.root ^ 2 *
        (gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1)).eval T.root +
      4 * (localClearedB68RhoOne g u (p.coeff 3)).eval T.root ^ 3 *
        (gZeroGlobalTangentC68 h0 g u (p.coeff 3)
          (p.coeff 2)).eval T.root +
      18 * (gZeroGlobalTangentC68 h0 g u (p.coeff 3)
          (p.coeff 2)).eval T.root ^ 2 *
        (gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1)).eval T.root =
      9 * (localClearedB68RhoOne g u (p.coeff 3)).eval T.root *
        (gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1)).eval T.root ^ 2 := by
  obtain ⟨i4, i3, hpack⟩ := T.rhoOne_gZeroChildGlobalClearedReduction
    hp hH hp6 hp5 hp4 hbeta hdelta hzeta
  dsimp only [RhoOneGZeroChildGlobalCleared68] at hpack
  obtain ⟨-, -, h3⟩ := hpack
  have hEval := congrArg (Polynomial.eval T.root) h3
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat,
    eval_C, eval_neg, T.root_eq] at hEval
  linear_combination (1 / 8 : k) * hEval

set_option maxHeartbeats 800000 in
/-- Source backwire: the eighth residual kept verbatim — every sibling,
the nonzero `G[-1]` boundary lane, the `C₂` face, the quadratic rays
and both refined children untouched — conjoined with the cleared
global reduction that replaces the remaining row tower on the
`G[-1] = 0` children. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenGlobalReductionResidual
    [IsAlgClosed k]
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hB : (↑(1 : ℚ) : WithTop ℚ) ≤
      (ratFuncAtHahn46 T.root T.source.B).orderTop)
    (hC : (0 : WithTop ℚ) ≤
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0)).orderTop)
    (hF : (0 : WithTop ℚ) ≤
      (rhoOneTangentDDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D)).orderTop)
    (hG : (↑(-1 : ℚ) : WithTop ℚ) ≤
      (rhoOneTangentEDefectHahn68
        (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E))).orderTop)
    (hbeta : T.source.beta = 0) (hdelta : T.source.delta = 0)
    (hzeta : T.source.zeta = 0) :
    (∃ i4 i3 : k,
      RhoOneGZeroChildGlobalCleared68 T.source.gamma T.source.epsilon
        i4 i3 h0 (localClearedA68RhoOne g u)
        (localClearedB68RhoOne g u (p.coeff 3))
        (gZeroGlobalTangentC68 h0 g u (p.coeff 3) (p.coeff 2))
        (gZeroGlobalTangentF68 h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1))
        (gZeroGlobalTangentG68 h0 g u (p.coeff 3) (p.coeff 2)
          (p.coeff 1) (p.coeff 0))) ∧
    (let AR : RatFunc k := T.source.A
     let BR : RatFunc k := T.source.B
     let CR : RatFunc k := T.source.C0 - RatFunc.C (1 / 3 : k) * AR ^ 2
     let FR : RatFunc k := T.source.D - RatFunc.C (1 / 3 : k) * AR * BR
     let GR : RatFunc k :=
       (T.source.E - RatFunc.C (1 / 27 : k) * AR ^ 3) -
         RatFunc.C (1 / 3 : k) * AR * CR
     let A := ratFuncAtHahn46 T.root T.source.A
     let B := ratFuncAtHahn46 T.root T.source.B
     let C := rhoOneCDefectHahn68 A
       (ratFuncAtHahn46 T.root T.source.C0)
     let F := rhoOneTangentDDefectHahn68 A B
       (ratFuncAtHahn46 T.root T.source.D)
     let G := rhoOneTangentEDefectHahn68 A C
       (rhoOneEDefectHahn68 A (ratFuncAtHahn46 T.root T.source.E))
     RhoOneDoubleZeroTerminalGBoundaryCapDerivativeNextResidual68
         T.root j T.source.gamma T.source.epsilon
         (localClearedA68RhoOne g u)
         (algebraMap k[X] (RatFunc k) h0) AR BR CR FR GR A B C F G ∨
       (G.coeff (-1 : ℚ) = 0 ∧ (0 : WithTop ℚ) ≤ G.orderTop ∧
         (RhoOneGZeroChildBGainRefinedEighth68 T.source.gamma
            T.source.epsilon T.source.A T.source.B T.source.C0
            T.source.D T.source.E A B C F G ∨
          RhoOneGZeroChildFGainRefinedEighth68 T.source.gamma
            T.source.epsilon T.source.A T.source.B T.source.C0
            T.source.D T.source.E A B C F G))) := by
  refine ⟨T.rhoOne_gZeroChildGlobalClearedReduction hp hH hp6 hp5 hp4
    hbeta hdelta hzeta, ?_⟩
  exact T.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenEighthResidual
    hp hH hp6 hp5 hp4 P hB hC hF hG hbeta hdelta hzeta

#print axioms rhoOneGZeroChildGlobalMinorFactored68
#print axioms SquareZeroLIntegratedLocalRootData68.rhoOne_gZeroGlobal_clearedTangentCoordinates
#print axioms SquareZeroLIntegratedLocalRootData68.rhoOne_gZeroChildGlobalClearedReduction
#print axioms SquareZeroLIntegratedLocalRootData68.rhoOne_gZeroChildGlobal_scaleDivisibility
#print axioms SquareZeroLIntegratedLocalRootData68.rhoOne_gZeroChildGlobal_rootTie
#print axioms SquareZeroLIntegratedLocalRootData68.rhoOne_exceptional_doubleZero_refinedGZero_terminalGBoundaryCapGZeroChildrenGlobalReductionResidual

end AlignedSquareGZeroChildGlobalReduction68

end Max11DegreeRoutes
