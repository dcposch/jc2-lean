import ArbitraryLoads

noncomputable section

/-! # Physical-scale early common-cubic boundary

The unit-pole argument in `Solution` takes `H = HahnSeries.single 1 h` and
the reconstructed source bounds `12 / k` and `18 / k`.  At a genuine weighted
pole of scale `p > 0` the same reconstruction is written in the physical Hahn
parameter `s = (k : ℚ) * p / 2`: the first-load monomial is
`H = HahnSeries.single s h`, the source regularity thresholds are the original
sextic weights `6 * p` and `9 * p`, and the higher-order errors sit strictly
beyond `s` and `3 * s / 2`.  The leading-order / cancellation analysis is the
direct physical-scale form of
`GCD369CubeEarlyCommonCubicBoundaryExclusion`; there is no reindexing
through the unit-pole theorems.
-/

/-- For every audited early weight the physical first-load order is strictly
below both original source-regularity thresholds. -/
theorem GCD369CubePhysicalBoundaryWeightAudit
    (k : ℕ) (hk : k ∈ ([1, 2, 4, 5, 7, 8, 10, 11] : List ℕ))
    {p s : ℚ} (hp : 0 < p) (hs : s = (k : ℚ) * p / 2) :
    s < 6 * p ∧ (3 : ℚ) * s / 2 < 9 * p := by
  have hklt : (k : ℚ) < 12 := by
    simp at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  subst s
  constructor <;> nlinarith

/-- Physical-scale leading-order dichotomy for the reconstructed `f`
boundary.  If the cubic has leading term `a * t^q` and the transverse normal
is a unit of residue `b`, then `K^2 + H * phi` has order at most `s` unless
the two terms have the same order and their leading coefficients cancel.
The only exceptional branch is therefore `q = s / 2` and `a^2 + h * b = 0`. -/
theorem GCD369CubePhysicalBoundaryLeadingOrderDichotomy
    {K : Type*} [Field K] [CharZero K]
    (s q : ℚ) (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    let A : HahnSeries ℚ K := HahnSeries.single q a
    let B : HahnSeries ℚ K := HahnSeries.single 0 b
    let H : HahnSeries ℚ K := HahnSeries.single s h
    (A ^ 2 + H * B).orderTop ≤ (↑s : WithTop ℚ) ∨
      q = s / 2 ∧ a ^ 2 + h * b = 0 := by
  dsimp only
  have hhb : h * b ≠ 0 := mul_ne_zero hh hb
  have hAorder :
      ((HahnSeries.single q a : HahnSeries ℚ K) ^ 2).orderTop =
        (↑(2 * q) : WithTop ℚ) := by
    rw [HahnSeries.single_pow, HahnSeries.orderTop_single (pow_ne_zero 2 ha)]
    simp [nsmul_eq_mul]
  have hBorder :
      ((HahnSeries.single s h : HahnSeries ℚ K) *
          HahnSeries.single 0 b).orderTop =
        (↑s : WithTop ℚ) := by
    rw [HahnSeries.single_mul_single, HahnSeries.orderTop_single hhb]
    simp
  by_cases hlo : 2 * q < s
  · left
    have horders :
        ((HahnSeries.single q a : HahnSeries ℚ K) ^ 2).orderTop <
          ((HahnSeries.single s h : HahnSeries ℚ K) *
            HahnSeries.single 0 b).orderTop := by
      rw [hAorder, hBorder]
      exact WithTop.coe_lt_coe.mpr hlo
    rw [HahnSeries.orderTop_add_eq_left horders, hAorder]
    exact WithTop.coe_le_coe.mpr (le_of_lt hlo)
  · by_cases hhi : s < 2 * q
    · left
      have horders :
          ((HahnSeries.single s h : HahnSeries ℚ K) *
              HahnSeries.single 0 b).orderTop <
            ((HahnSeries.single q a : HahnSeries ℚ K) ^ 2).orderTop := by
        rw [hAorder, hBorder]
        exact WithTop.coe_lt_coe.mpr hhi
      rw [HahnSeries.orderTop_add_eq_right horders, hBorder]
    · have htwoq : 2 * q = s :=
        le_antisymm (le_of_not_gt hhi) (le_of_not_gt hlo)
      have hq : q = s / 2 := by linarith
      by_cases hcancel : a ^ 2 + h * b = 0
      · exact Or.inr ⟨hq, hcancel⟩
      · left
        subst q
        have htwo : (2 : ℕ) • (s / 2) = s := by
          simp [nsmul_eq_mul]; ring
        have hseries :
            (HahnSeries.single (s / 2) a : HahnSeries ℚ K) ^ 2 +
                HahnSeries.single s h * HahnSeries.single 0 b =
              HahnSeries.single s (a ^ 2 + h * b) := by
          rw [HahnSeries.single_pow, HahnSeries.single_mul_single, htwo,
            add_zero]
          exact (HahnSeries.single_add s (a ^ 2) (h * b)).symm
        rw [hseries, HahnSeries.orderTop_single hcancel]

/-- In the only possible first-order cancellation regime, where the cubic
has physical order `s / 2` and `K^2 + H * phi` cancels, the leading term of
`K^3 + (3 / 2) H K phi` has exact order `3 * s / 2`. -/
theorem GCD369CubePhysicalBoundaryCancellationOrder
    {K : Type*} [Field K] [CharZero K]
    (s : ℚ) (a b h : K) (ha : a ≠ 0)
    (hcancel : a ^ 2 + h * b = 0) :
    let A : HahnSeries ℚ K := HahnSeries.single (s / 2) a
    let B : HahnSeries ℚ K := HahnSeries.single 0 b
    let H : HahnSeries ℚ K := HahnSeries.single s h
    let C32 : HahnSeries ℚ K := HahnSeries.single 0 (3 / 2)
    (A ^ 3 + C32 * H * A * B).order = 3 * s / 2 := by
  dsimp only
  have hcoefficient : a ^ 3 + (3 / 2) * h * a * b ≠ 0 := by
    have heq : a ^ 3 + (3 / 2) * h * a * b = (-1 / 2) * a ^ 3 := by
      linear_combination (3 / 2 * a) * hcancel
    rw [heq]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 ha)
  have h3 : (3 : ℕ) • (s / 2) = 3 * s / 2 := by
    simp [nsmul_eq_mul]; ring
  have hsum : (0 : ℚ) + s + s / 2 + 0 = 3 * s / 2 := by ring
  have hseries :
      (HahnSeries.single (s / 2) a : HahnSeries ℚ K) ^ 3 +
          HahnSeries.single 0 (3 / 2 : K) * HahnSeries.single s h *
            HahnSeries.single (s / 2) a * HahnSeries.single 0 b =
        HahnSeries.single (3 * s / 2)
          (a ^ 3 + (3 / 2) * h * a * b) := by
    rw [HahnSeries.single_pow, HahnSeries.single_mul_single,
      HahnSeries.single_mul_single, HahnSeries.single_mul_single, h3, hsum]
    exact (HahnSeries.single_add (3 * s / 2)
      (a ^ 3) ((3 / 2) * h * a * b)).symm
  rw [hseries, HahnSeries.order_single hcoefficient]

/-- Terms of strictly larger physical order cannot cancel the forced
`3 * s / 2` boundary term. -/
theorem GCD369CubePhysicalBoundaryCancellationOrderWithHigherTerms
    {K : Type*} [Field K] [CharZero K]
    (s : ℚ) (a b h : K) (ha : a ≠ 0)
    (hcancel : a ^ 2 + h * b = 0)
    (E : HahnSeries ℚ K)
    (hE : (↑((3 : ℚ) * s / 2) : WithTop ℚ) < E.orderTop) :
    let A : HahnSeries ℚ K := HahnSeries.single (s / 2) a
    let B : HahnSeries ℚ K := HahnSeries.single 0 b
    let H : HahnSeries ℚ K := HahnSeries.single s h
    let C32 : HahnSeries ℚ K := HahnSeries.single 0 (3 / 2)
    (A ^ 3 + C32 * H * A * B + E).orderTop =
      (↑((3 : ℚ) * s / 2) : WithTop ℚ) := by
  dsimp only
  let G : HahnSeries ℚ K :=
    HahnSeries.single (s / 2) a ^ 3 +
      HahnSeries.single 0 (3 / 2) * HahnSeries.single s h *
        HahnSeries.single (s / 2) a * HahnSeries.single 0 b
  change (G + E).orderTop = (↑((3 : ℚ) * s / 2) : WithTop ℚ)
  have hGorder : G.order = (3 : ℚ) * s / 2 := by
    simpa [G] using
      GCD369CubePhysicalBoundaryCancellationOrder s a b h ha hcancel
  have hcoefficient : a ^ 3 + (3 / 2) * h * a * b ≠ 0 := by
    have heq : a ^ 3 + (3 / 2) * h * a * b = (-1 / 2) * a ^ 3 := by
      linear_combination (3 / 2 * a) * hcancel
    rw [heq]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 ha)
  have h3 : (3 : ℕ) • (s / 2) = 3 * s / 2 := by
    simp [nsmul_eq_mul]; ring
  have hsum : (0 : ℚ) + s + s / 2 + 0 = 3 * s / 2 := by ring
  have hGeq :
      G = HahnSeries.single (3 * s / 2)
        (a ^ 3 + (3 / 2) * h * a * b) := by
    dsimp [G]
    rw [HahnSeries.single_pow, HahnSeries.single_mul_single,
      HahnSeries.single_mul_single, HahnSeries.single_mul_single, h3, hsum]
    exact (HahnSeries.single_add (3 * s / 2)
      (a ^ 3) ((3 / 2) * h * a * b)).symm
  have hGne : G ≠ 0 := by
    rw [hGeq]
    exact HahnSeries.single_ne_zero hcoefficient
  have hGtop : G.orderTop = (↑((3 : ℚ) * s / 2) : WithTop ℚ) := by
    calc
      G.orderTop = (G.order : WithTop ℚ) :=
        (HahnSeries.order_eq_orderTop_of_ne_zero hGne).symm
      _ = (↑((3 : ℚ) * s / 2) : WithTop ℚ) :=
        congrArg (fun q : ℚ => (q : WithTop ℚ)) hGorder
  have hGE : G.orderTop < E.orderTop := by
    rw [hGtop]
    exact hE
  calc
    (G + E).orderTop = G.orderTop := HahnSeries.orderTop_add_eq_left hGE
    _ = (↑((3 : ℚ) * s / 2) : WithTop ℚ) := hGtop

/-- A source value required to vanish to order strictly greater than
`3 * s / 2` cannot contain the forced cancellation term plus only
higher-order errors. -/
theorem GCD369CubePhysicalBoundaryRegularityContradiction
    {K : Type*} [Field K] [CharZero K]
    (s : ℚ) (a b h : K) (ha : a ≠ 0)
    (hcancel : a ^ 2 + h * b = 0)
    (E : HahnSeries ℚ K)
    (hE : (↑((3 : ℚ) * s / 2) : WithTop ℚ) < E.orderTop)
    (required : WithTop ℚ)
    (hrequired : (↑((3 : ℚ) * s / 2) : WithTop ℚ) < required)
    (hregular : required ≤
      let A : HahnSeries ℚ K := HahnSeries.single (s / 2) a
      let B : HahnSeries ℚ K := HahnSeries.single 0 b
      let H : HahnSeries ℚ K := HahnSeries.single s h
      let C32 : HahnSeries ℚ K := HahnSeries.single 0 (3 / 2)
      (A ^ 3 + C32 * H * A * B + E).orderTop) :
    False := by
  have horder :=
    GCD369CubePhysicalBoundaryCancellationOrderWithHigherTerms
      s a b h ha hcancel E hE
  rw [horder] at hregular
  exact (not_le_of_gt hrequired) hregular

/-- The cancellation branch contradicts the original `g`-boundary order for
every early forced load at physical scale.  Weight twelve is absent: it is
the first equality case. -/
theorem GCD369CubePhysicalEarlyBoundaryRegularityContradiction
    {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (hk : k ∈ ([1, 2, 4, 5, 7, 8, 10, 11] : List ℕ))
    (p s : ℚ) (hp : 0 < p) (hs : s = (k : ℚ) * p / 2)
    (a b h : K) (ha : a ≠ 0)
    (hcancel : a ^ 2 + h * b = 0)
    (E : HahnSeries ℚ K)
    (hE : (↑((3 : ℚ) * s / 2) : WithTop ℚ) < E.orderTop)
    (hregular : (↑((9 : ℚ) * p) : WithTop ℚ) ≤
      let A : HahnSeries ℚ K := HahnSeries.single (s / 2) a
      let B : HahnSeries ℚ K := HahnSeries.single 0 b
      let H : HahnSeries ℚ K := HahnSeries.single s h
      let C32 : HahnSeries ℚ K := HahnSeries.single 0 (3 / 2)
      (A ^ 3 + C32 * H * A * B + E).orderTop) :
    False := by
  have hstrict : (3 : ℚ) * s / 2 < 9 * p :=
    (GCD369CubePhysicalBoundaryWeightAudit k hk hp hs).2
  have hstrictTop :
      (↑((3 : ℚ) * s / 2) : WithTop ℚ) < (↑((9 : ℚ) * p) : WithTop ℚ) :=
    WithTop.coe_lt_coe.mpr hstrict
  exact GCD369CubePhysicalBoundaryRegularityContradiction
    s a b h ha hcancel E hE (↑((9 : ℚ) * p) : WithTop ℚ) hstrictTop hregular

/-- The full physical-scale early-boundary obstruction, including both
noncancellation branches.  Higher-order errors cannot alter a leading `f`
term of order at most `s`; in the unique cancellation branch, the
corresponding `g` term has forced order `3 * s / 2`.  The strict source
bounds `6 * p` and `9 * p` for every weight below twelve therefore cannot
hold simultaneously. -/
theorem GCD369CubePhysicalEarlyBoundaryLeadingOrderContradiction
    {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (hk : k ∈ ([1, 2, 4, 5, 7, 8, 10, 11] : List ℕ))
    (p s : ℚ) (hp : 0 < p) (hs : s = (k : ℚ) * p / 2)
    (q : ℚ) (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    (EF EG : HahnSeries ℚ K)
    (hEF : (↑s : WithTop ℚ) < EF.orderTop)
    (hEG : (↑((3 : ℚ) * s / 2) : WithTop ℚ) < EG.orderTop)
    (hfregular : (↑((6 : ℚ) * p) : WithTop ℚ) ≤
      let A : HahnSeries ℚ K := HahnSeries.single q a
      let B : HahnSeries ℚ K := HahnSeries.single 0 b
      let H : HahnSeries ℚ K := HahnSeries.single s h
      (A ^ 2 + H * B + EF).orderTop)
    (hgregular : (↑((9 : ℚ) * p) : WithTop ℚ) ≤
      let A : HahnSeries ℚ K := HahnSeries.single q a
      let B : HahnSeries ℚ K := HahnSeries.single 0 b
      let H : HahnSeries ℚ K := HahnSeries.single s h
      let C32 : HahnSeries ℚ K := HahnSeries.single 0 (3 / 2)
      (A ^ 3 + C32 * H * A * B + EG).orderTop) :
    False := by
  rcases GCD369CubePhysicalBoundaryLeadingOrderDichotomy s q a b h ha hb hh
    with hflow | ⟨hq, hcancel⟩
  · have horders :
        ((HahnSeries.single q a : HahnSeries ℚ K) ^ 2 +
            HahnSeries.single s h * HahnSeries.single 0 b).orderTop <
          EF.orderTop := lt_of_le_of_lt hflow hEF
    have hsum := HahnSeries.orderTop_add_eq_left horders
    dsimp only at hfregular
    rw [hsum] at hfregular
    have hrequired :
        (↑s : WithTop ℚ) < (↑((6 : ℚ) * p) : WithTop ℚ) :=
      WithTop.coe_lt_coe.mpr
        (GCD369CubePhysicalBoundaryWeightAudit k hk hp hs).1
    exact (not_le_of_gt hrequired) (hfregular.trans hflow)
  · subst q
    exact GCD369CubePhysicalEarlyBoundaryRegularityContradiction
      k hk p s hp hs a b h ha hcancel EG hEG hgregular

/-- Source-coordinate form of the complete physical-scale early-boundary
obstruction.  A limiting root of the common cubic cannot also annihilate
the certified normal, so the normal value is a unit and the Hahn-series
dichotomy applies with its actual value `X * r^2 + Y * r + Z`. -/
theorem GCD369CubePhysicalEarlyCommonCubicBoundaryExclusion
    {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (hk : k ∈ ([1, 2, 4, 5, 7, 8, 10, 11] : List ℕ))
    (p s : ℚ) (hp : 0 < p) (hs : s = (k : ℚ) * p / 2)
    (q : ℚ) (a h Xn Yn Zn u v r : K) (ha : a ≠ 0) (hh : h ≠ 0)
    (hnocommon : ∀ z : K, z ^ 3 + u * z + v = 0 →
      Xn * z ^ 2 + Yn * z + Zn = 0 → False)
    (hKroot : r ^ 3 + u * r + v = 0)
    (EF EG : HahnSeries ℚ K)
    (hEF : (↑s : WithTop ℚ) < EF.orderTop)
    (hEG : (↑((3 : ℚ) * s / 2) : WithTop ℚ) < EG.orderTop)
    (hfregular : (↑((6 : ℚ) * p) : WithTop ℚ) ≤
      let A : HahnSeries ℚ K := HahnSeries.single q a
      let B : HahnSeries ℚ K := HahnSeries.single 0
        (Xn * r ^ 2 + Yn * r + Zn)
      let H : HahnSeries ℚ K := HahnSeries.single s h
      (A ^ 2 + H * B + EF).orderTop)
    (hgregular : (↑((9 : ℚ) * p) : WithTop ℚ) ≤
      let A : HahnSeries ℚ K := HahnSeries.single q a
      let B : HahnSeries ℚ K := HahnSeries.single 0
        (Xn * r ^ 2 + Yn * r + Zn)
      let H : HahnSeries ℚ K := HahnSeries.single s h
      let C32 : HahnSeries ℚ K := HahnSeries.single 0 (3 / 2)
      (A ^ 3 + C32 * H * A * B + EG).orderTop) :
    False := by
  have hb : Xn * r ^ 2 + Yn * r + Zn ≠ 0 := by
    intro hphi
    exact hnocommon r hKroot hphi
  exact GCD369CubePhysicalEarlyBoundaryLeadingOrderContradiction
    k hk p s hp hs q a (Xn * r ^ 2 + Yn * r + Zn) h ha hb hh EF EG
      hEF hEG hfregular hgregular

/-- Concrete physical-scale source data for an early common-cubic pole
landing, retaining the actual nonzero Faber load.  The first-load monomial
is the physical Hahn parameter `s = (load.weight : ℚ) * p / 2`, not the
unit-pole generator. -/
structure GCD369CubePhysicalFaberEarlyBoundaryData
    (K : Type*) [Field K] where
  Xn : K
  Yn : K
  Zn : K
  u : K
  v : K
  load : GCD369CubeArbitraryEarlyFaberLoad Xn Yn Zn u v
  p : ℚ
  hp : 0 < p
  s : ℚ
  hs : s = (load.weight : ℚ) * p / 2
  q : ℚ
  a : K
  h : K
  r : K
  EF : HahnSeries ℚ K
  EG : HahnSeries ℚ K
  ha : a ≠ 0
  hh : h ≠ 0
  hKroot : r ^ 3 + u * r + v = 0
  hEF : (↑s : WithTop ℚ) < EF.orderTop
  hEG : (↑((3 : ℚ) * s / 2) : WithTop ℚ) < EG.orderTop
  hfregular : (↑((6 : ℚ) * p) : WithTop ℚ) ≤
    let A : HahnSeries ℚ K := HahnSeries.single q a
    let B : HahnSeries ℚ K := HahnSeries.single 0
      (Xn * r ^ 2 + Yn * r + Zn)
    let H : HahnSeries ℚ K := HahnSeries.single s h
    (A ^ 2 + H * B + EF).orderTop
  hgregular : (↑((9 : ℚ) * p) : WithTop ℚ) ≤
    let A : HahnSeries ℚ K := HahnSeries.single q a
    let B : HahnSeries ℚ K := HahnSeries.single 0
      (Xn * r ^ 2 + Yn * r + Zn)
    let H : HahnSeries ℚ K := HahnSeries.single s h
    let C32 : HahnSeries ℚ K := HahnSeries.single 0 (3 / 2)
    (A ^ 3 + C32 * H * A * B + EG).orderTop

/-- Every arbitrary nonzero early Faber landing at physical Hahn scale
violates the original source boundary inequalities. -/
theorem GCD369CubePhysicalFaberEarlyBoundaryDataEmpty
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (D : GCD369CubePhysicalFaberEarlyBoundaryData K) : False := by
  exact GCD369CubePhysicalEarlyCommonCubicBoundaryExclusion
    D.load.weight D.load.weight_mem D.p D.s D.hp D.hs
    D.q D.a D.h D.Xn D.Yn D.Zn D.u D.v D.r D.ha D.hh
    D.load.noCommonRoot D.hKroot D.EF D.EG D.hEF D.hEG
    D.hfregular D.hgregular

#print axioms GCD369CubePhysicalEarlyCommonCubicBoundaryExclusion
#print axioms GCD369CubePhysicalFaberEarlyBoundaryDataEmpty
