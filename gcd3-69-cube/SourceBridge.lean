import ArbitraryLoads

noncomputable section

universe u

/-! # First source-to-trajectory bridge

This module begins the non-circular producer required before the finite
landing theorem can be applied to a cube-core source.  Its input is the actual
leading Faber point and the four vanishing invariant equations, not a choice
of landing constructor.  The output is the exhaustive common-cubic versus
Davenport--Stothers component split, with projective nonvanishing derived
internally.
-/

/-- A nonzero leading coefficient point satisfying the four exact zero-high
Faber equations. -/
structure GCD369CubeLeadingFaberSource (K : Type u) [Field K] where
  a0 : K
  a1 : K
  a2 : K
  a3 : K
  a4 : K
  hnonzero : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0 ∨ a3 ≠ 0 ∨ a4 ≠ 0
  hr1 : GCD369CubeFaberR1 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 = 0
  hr2 : GCD369CubeFaberR2 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 = 0
  hr3 : GCD369CubeFaberR3 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 = 0
  hr4 : GCD369CubeFaberR4 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 = 0

/-- The two reduced projective components of the leading Faber source. -/
inductive GCD369CubeLeadingComponent {K : Type u} [Field K]
    (a0 a1 a2 a3 a4 : K) : Prop where
  | common (u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
      (ha4 : a4 = 2 * u) (ha3 : a3 = 2 * v) (ha2 : a2 = u ^ 2)
      (ha1 : a1 = 2 * u * v) (ha0 : a0 = v ^ 2)
  | davenportStothers (lambda : K) (hlambda : lambda ≠ 0)
      (ha4 : a4 = 4 * lambda) (ha3 : a3 = 0)
      (ha2 : a2 = 10 * lambda ^ 2) (ha1 : a1 = 0)
      (ha0 : a0 = 6 * lambda ^ 3)

/-- Exact source equations produce one of the two projective leading
components.  Neither component is selected or assumed by the caller. -/
theorem GCD369CubeLeadingFaberSource.toComponent
    {K : Type u} [Field K] [CharZero K]
    (S : GCD369CubeLeadingFaberSource K) :
    GCD369CubeLeadingComponent S.a0 S.a1 S.a2 S.a3 S.a4 := by
  rcases GCD369CubeFaberLeadingComponentClassification
      S.a0 S.a1 S.a2 S.a3 S.a4 S.hr1 S.hr2 S.hr3 S.hr4 with
    hcommon | hds
  · rcases hcommon with ⟨u, v, ha4, ha3, ha2, ha1, ha0⟩
    have hprojective : u ≠ 0 ∨ v ≠ 0 := by
      by_contra huv
      push Not at huv
      rcases huv with ⟨hu, hv⟩
      have hnonzero := S.hnonzero
      rw [ha0, ha1, ha2, ha3, ha4] at hnonzero
      simp [hu, hv] at hnonzero
    exact .common u v hprojective ha4 ha3 ha2 ha1 ha0
  · rcases hds with ⟨lambda, ha4, ha3, ha2, ha1, ha0⟩
    have hlambda : lambda ≠ 0 := by
      intro hlambda
      have hnonzero := S.hnonzero
      rw [ha0, ha1, ha2, ha3, ha4] at hnonzero
      simp [hlambda] at hnonzero
    exact .davenportStothers lambda hlambda ha4 ha3 ha2 ha1 ha0

/-! ## Automatic first-load routing on the common-cubic component -/

/-- The actual ordered early Faber jet at a common-cubic leading point.
Each conditional row says what the source coefficient equations become when
that coordinate is the first nonzero load; no landing constructor is selected
by the caller. -/
structure GCD369CubeEarlyFaberJetSource (K : Type u) [Field K] where
  Xn : K
  Yn : K
  Zn : K
  u : K
  v : K
  hprojective : u ≠ 0 ∨ v ≠ 0
  d : K
  c7 : K
  c5 : K
  c4 : K
  c2 : K
  c1 : K
  rho1 : K
  rho2 : K
  hd : d ≠ 0 → GCD369CubeDLeadingFaberRowsAt Xn Yn Zn u v d
  hc7 : d = 0 → c7 ≠ 0 →
    GCD369CubeC7LeadingFaberRowsAt Xn Yn Zn u v c7
  hc5 : d = 0 → c7 = 0 → c5 ≠ 0 →
    GCD369CubeC5LeadingFaberRowsAt Xn Yn Zn u v c5
  hc4 : d = 0 → c7 = 0 → c5 = 0 → c4 ≠ 0 →
    GCD369CubeC4LeadingFaberRowsAt Xn Yn Zn u v c4
  hc2 : d = 0 → c7 = 0 → c5 = 0 → c4 = 0 → c2 ≠ 0 →
    GCD369CubeC2LeadingFaberRowsAt Xn Yn Zn u v c2
  hc1 : d = 0 → c7 = 0 → c5 = 0 → c4 = 0 → c2 = 0 →
    c1 ≠ 0 → GCD369CubeC1LeadingFaberRowsAt Xn Yn Zn u v c1
  hrho1 : d = 0 → c7 = 0 → c5 = 0 → c4 = 0 → c2 = 0 →
    c1 = 0 → rho1 ≠ 0 →
    GCD369CubeRhoOneLeadingFaberRowsAt Xn Yn Zn u v rho1
  hrho2 : d = 0 → c7 = 0 → c5 = 0 → c4 = 0 → c2 = 0 →
    c1 = 0 → rho1 = 0 → rho2 ≠ 0 →
    GCD369CubeRhoTwoLeadingFaberRowsAt Xn Yn Zn u v rho2

namespace GCD369CubeEarlyFaberJetSource

/-- Weight of the first nonzero early source/target coefficient, with zero
reserved for the later-fibre case in which all eight coefficients vanish. -/
noncomputable def firstWeight {K : Type u} [Field K]
    (S : GCD369CubeEarlyFaberJetSource K) : ℕ := by
  classical
  exact if S.d ≠ 0 then 1 else if S.c7 ≠ 0 then 2 else
    if S.c5 ≠ 0 then 4 else if S.c4 ≠ 0 then 5 else
    if S.c2 ≠ 0 then 7 else if S.c1 ≠ 0 then 8 else
    if S.rho1 ≠ 0 then 10 else if S.rho2 ≠ 0 then 11 else 0

/-- The ordered jet either constructs its own arbitrary-load Faber
alternative, at the computed weight, or all early coefficients vanish.
This is the finite source-to-landing choice missing from the earlier API. -/
theorem toArbitraryLoad_or_allZero {K : Type u} [Field K]
    (S : GCD369CubeEarlyFaberJetSource K) :
    (∃ L : GCD369CubeArbitraryEarlyFaberLoad
        S.Xn S.Yn S.Zn S.u S.v, L.weight = S.firstWeight) ∨
      (S.d = 0 ∧ S.c7 = 0 ∧ S.c5 = 0 ∧ S.c4 = 0 ∧
        S.c2 = 0 ∧ S.c1 = 0 ∧ S.rho1 = 0 ∧ S.rho2 = 0) := by
  by_cases hd : S.d ≠ 0
  · left
    refine ⟨GCD369CubeArbitraryEarlyFaberLoad.d S.d hd S.hprojective
      (S.hd hd), ?_⟩
    simp [firstWeight, hd, GCD369CubeArbitraryEarlyFaberLoad.weight]
  · have hd0 : S.d = 0 := not_ne_iff.mp hd
    by_cases hc7 : S.c7 ≠ 0
    · left
      refine ⟨GCD369CubeArbitraryEarlyFaberLoad.c7 S.c7 hc7 S.hprojective
        (S.hc7 hd0 hc7), ?_⟩
      simp [firstWeight, hd, hc7, GCD369CubeArbitraryEarlyFaberLoad.weight]
    · have hc70 : S.c7 = 0 := not_ne_iff.mp hc7
      by_cases hc5 : S.c5 ≠ 0
      · left
        refine ⟨GCD369CubeArbitraryEarlyFaberLoad.c5 S.c5 hc5 S.hprojective
          (S.hc5 hd0 hc70 hc5), ?_⟩
        simp [firstWeight, hd, hc7, hc5,
          GCD369CubeArbitraryEarlyFaberLoad.weight]
      · have hc50 : S.c5 = 0 := not_ne_iff.mp hc5
        by_cases hc4 : S.c4 ≠ 0
        · left
          refine ⟨GCD369CubeArbitraryEarlyFaberLoad.c4 S.c4 hc4 S.hprojective
            (S.hc4 hd0 hc70 hc50 hc4), ?_⟩
          simp [firstWeight, hd, hc7, hc5, hc4,
            GCD369CubeArbitraryEarlyFaberLoad.weight]
        · have hc40 : S.c4 = 0 := not_ne_iff.mp hc4
          by_cases hc2 : S.c2 ≠ 0
          · left
            refine ⟨GCD369CubeArbitraryEarlyFaberLoad.c2 S.c2 hc2 S.hprojective
              (S.hc2 hd0 hc70 hc50 hc40 hc2), ?_⟩
            simp [firstWeight, hd, hc7, hc5, hc4, hc2,
              GCD369CubeArbitraryEarlyFaberLoad.weight]
          · have hc20 : S.c2 = 0 := not_ne_iff.mp hc2
            by_cases hc1 : S.c1 ≠ 0
            · left
              refine ⟨GCD369CubeArbitraryEarlyFaberLoad.c1 S.c1 hc1
                S.hprojective (S.hc1 hd0 hc70 hc50 hc40 hc20 hc1), ?_⟩
              simp [firstWeight, hd, hc7, hc5, hc4, hc2, hc1,
                GCD369CubeArbitraryEarlyFaberLoad.weight]
            · have hc10 : S.c1 = 0 := not_ne_iff.mp hc1
              by_cases hrho1 : S.rho1 ≠ 0
              · left
                refine ⟨GCD369CubeArbitraryEarlyFaberLoad.rhoOne S.rho1
                  hrho1 S.hprojective
                  (S.hrho1 hd0 hc70 hc50 hc40 hc20 hc10 hrho1), ?_⟩
                simp [firstWeight, hd, hc7, hc5, hc4, hc2, hc1, hrho1,
                  GCD369CubeArbitraryEarlyFaberLoad.weight]
              · have hrho10 : S.rho1 = 0 := not_ne_iff.mp hrho1
                by_cases hrho2 : S.rho2 ≠ 0
                · left
                  refine ⟨GCD369CubeArbitraryEarlyFaberLoad.rhoTwo S.rho2
                    hrho2 S.hprojective
                    (S.hrho2 hd0 hc70 hc50 hc40 hc20 hc10 hrho10 hrho2), ?_⟩
                  simp [firstWeight, hd, hc7, hc5, hc4, hc2, hc1, hrho1,
                    hrho2, GCD369CubeArbitraryEarlyFaberLoad.weight]
                · right
                  exact ⟨hd0, hc70, hc50, hc40, hc20, hc10, hrho10,
                    not_ne_iff.mp hrho2⟩

end GCD369CubeEarlyFaberJetSource

/-- Original boundary data attached to an ordered early Faber jet.  The
regularity thresholds use the computed first weight, not a caller-provided
landing label. -/
structure GCD369CubeEarlyFaberBoundarySource
    (K : Type u) [Field K] where
  jet : GCD369CubeEarlyFaberJetSource K
  hactive : jet.firstWeight ≠ 0
  q : ℚ
  a : K
  h : K
  r : K
  EF : HahnSeries ℚ K
  EG : HahnSeries ℚ K
  ha : a ≠ 0
  hh : h ≠ 0
  hKroot : r ^ 3 + jet.u * r + jet.v = 0
  hEF : (↑(1 : ℚ) : WithTop ℚ) < EF.orderTop
  hEG : (↑(3 / 2 : ℚ) : WithTop ℚ) < EG.orderTop
  hfregular :
    (↑((12 : ℚ) / jet.firstWeight) : WithTop ℚ) ≤
      let A : HahnSeries ℚ K := HahnSeries.single q a
      let B : HahnSeries ℚ K := HahnSeries.single 0
        (jet.Xn * r ^ 2 + jet.Yn * r + jet.Zn)
      let H : HahnSeries ℚ K := HahnSeries.single 1 h
      (A ^ 2 + H * B + EF).orderTop
  hgregular :
    (↑((18 : ℚ) / jet.firstWeight) : WithTop ℚ) ≤
      let A : HahnSeries ℚ K := HahnSeries.single q a
      let B : HahnSeries ℚ K := HahnSeries.single 0
        (jet.Xn * r ^ 2 + jet.Yn * r + jet.Zn)
      let H : HahnSeries ℚ K := HahnSeries.single 1 h
      let C32 : HahnSeries ℚ K := HahnSeries.single 0 (3 / 2)
      (A ^ 3 + C32 * H * A * B + EG).orderTop

/-- Every active ordered early Faber source automatically lands in the
arbitrary-load boundary obstruction and is therefore impossible. -/
theorem GCD369CubeEarlyFaberBoundarySource.empty
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (S : GCD369CubeEarlyFaberBoundarySource K) : False := by
  rcases S.jet.toArbitraryLoad_or_allZero with hload | hzero
  · obtain ⟨L, hweight⟩ := hload
    apply GCD369CubeArbitraryFaberEarlyBoundaryDataEmpty
      ({
        Xn := S.jet.Xn
        Yn := S.jet.Yn
        Zn := S.jet.Zn
        u := S.jet.u
        v := S.jet.v
        load := L
        q := S.q
        a := S.a
        h := S.h
        r := S.r
        EF := S.EF
        EG := S.EG
        ha := S.ha
        hh := S.hh
        hKroot := S.hKroot
        hEF := S.hEF
        hEG := S.hEG
        hfregular := by simpa [hweight] using S.hfregular
        hgregular := by simpa [hweight] using S.hgregular
      } : GCD369CubeArbitraryFaberEarlyBoundaryData K)
  · rcases hzero with ⟨hd, hc7, hc5, hc4, hc2, hc1, hrho1, hrho2⟩
    apply S.hactive
    simp [GCD369CubeEarlyFaberJetSource.firstWeight, hd, hc7, hc5, hc4,
      hc2, hc1, hrho1, hrho2]

/-! ## Exact handoff to the mixed later-invariant fibre -/

/-- The zero-high-constant Faber fibre after the early target loads have
vanished.  The two surviving invariant values are retained as actual values
of `r3` and `r4`, rather than as a caller-selected elliptic or cusp branch. -/
structure GCD369CubeLaterInvariantSource (K : Type u) [Field K] where
  a0 : K
  a1 : K
  a2 : K
  a3 : K
  a4 : K
  rho3 : K
  rho4 : K
  hr1 : GCD369CubeFaberR1 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 = 0
  hr2 : GCD369CubeFaberR2 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 = 0
  hr3 : GCD369CubeFaberR3 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 = rho3
  hr4 : GCD369CubeFaberR4 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 = rho4

namespace GCD369CubeLaterInvariantSource

set_option maxHeartbeats 4000000 in
/-- If the last invariant is nonzero, the source itself enters the localized
mixed fibre.  The coordinates `A,B,w,V` are computed from the original five
Faber coefficients.  In particular `A != 0` is proved, and the exact cubic
and terminal formulas are consequences of the two earlier invariant rows;
no mixed-fibre landing is assumed by the caller. -/
theorem mixedCoordinates {K : Type u} [Field K] [CharZero K]
    (S : GCD369CubeLaterInvariantSource K) (hrho4 : S.rho4 ≠ 0) :
    let A := 4 * S.a2 - S.a4 ^ 2
    let B := 2 * S.a1 - S.a3 * S.a4
    let w := 4 * S.a0 - S.a3 ^ 2
    let V := w + 8 * B ^ 2 / A
    A ≠ 0 ∧
      S.rho4 = -3 * A ^ 2 * B / 512 ∧
      S.rho3 = (24 * V ^ 2 - A ^ 3) / 1024 ∧
      GCD369CubeFaberR5 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
        A * (A * V - 12 * B ^ 2) / 1024 := by
  dsimp only
  let A : K := 4 * S.a2 - S.a4 ^ 2
  let B : K := 2 * S.a1 - S.a3 * S.a4
  let w : K := 4 * S.a0 - S.a3 ^ 2
  let V : K := w + 8 * B ^ 2 / A
  have he4 : -A ^ 2 * S.a4 + 4 * A * w + 8 * B ^ 2 = 0 := by
    have hid :
        -A ^ 2 * S.a4 + 4 * A * w + 8 * B ^ 2 =
          (256 / 3 : K) *
            GCD369CubeFaberR1 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 := by
      dsimp [A, B, w, GCD369CubeFaberR1]
      ring
    rw [hid, S.hr1]
    ring
  have he3 :
      -A ^ 2 * S.a3 - 4 * A * B * S.a4 + 8 * B * w = 0 := by
    have hid :
        -A ^ 2 * S.a3 - 4 * A * B * S.a4 + 8 * B * w =
          (256 / 3 : K) *
            GCD369CubeFaberR2 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 := by
      dsimp [A, B, w, GCD369CubeFaberR2]
      ring
    rw [hid, S.hr2]
    ring
  have hr3compact :
      GCD369CubeFaberR3 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
        -(A ^ 3 - 4 * A ^ 2 * S.a4 ^ 2 + 48 * A * B * S.a3 +
          16 * A * S.a4 * w + 32 * B ^ 2 * S.a4 - 24 * w ^ 2) / 1024 := by
    dsimp [A, B, w, GCD369CubeFaberR3]
    ring
  have hr4compact :
      GCD369CubeFaberR4 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
        (-3 * A ^ 2 * B + 3 * A ^ 2 * S.a3 * S.a4 +
          4 * A * B * S.a4 ^ 2 - 8 * A * S.a3 * w -
          16 * B ^ 2 * S.a3 - 8 * B * S.a4 * w) / 512 := by
    dsimp [A, B, w, GCD369CubeFaberR4]
    ring
  have hr5compact :
      GCD369CubeFaberR5 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
        (3 * A ^ 3 * S.a4 + 12 * A ^ 2 * S.a3 ^ 2 -
          2 * A ^ 2 * S.a4 ^ 3 - 6 * A ^ 2 * w - 48 * A * B ^ 2 +
          48 * A * B * S.a3 * S.a4 + 8 * A * S.a4 ^ 2 * w +
          16 * B ^ 2 * S.a4 ^ 2 - 96 * B * S.a3 * w) / 6144 := by
    dsimp [A, B, w, GCD369CubeFaberR5]
    ring
  have hrho4rel : A ^ 2 * B + (256 / 9 : K) * (6 * S.rho4) = 0 := by
    have hid :
        A ^ 2 * B + (256 / 9 : K) *
            (6 * GCD369CubeFaberR4
              S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0) =
          (-2 * S.a3 / 3) *
              (-A ^ 2 * S.a4 + 4 * A * w + 8 * B ^ 2) +
            (-S.a4 / 3) *
              (-A ^ 2 * S.a3 - 4 * A * B * S.a4 + 8 * B * w) := by
      rw [hr4compact]
      ring
    calc
      A ^ 2 * B + (256 / 9 : K) * (6 * S.rho4) =
          A ^ 2 * B + (256 / 9 : K) *
            (6 * GCD369CubeFaberR4
              S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0) := by rw [S.hr4]
      _ = (-2 * S.a3 / 3) *
              (-A ^ 2 * S.a4 + 4 * A * w + 8 * B ^ 2) +
            (-S.a4 / 3) *
              (-A ^ 2 * S.a3 - 4 * A * B * S.a4 + 8 * B * w) := hid
      _ = 0 := by rw [he4, he3]; ring
  have hA : A ≠ 0 := by
    intro hA
    rw [hA] at hrho4rel
    norm_num at hrho4rel
    exact hrho4 hrho4rel
  have hrho4formula : S.rho4 = -3 * A ^ 2 * B / 512 := by
    linear_combination (3 / 512 : K) * hrho4rel
  have hrho3formula : S.rho3 = (24 * V ^ 2 - A ^ 3) / 1024 := by
    rw [← S.hr3]
    rw [hr3compact]
    dsimp only [V]
    field_simp [hA]
    linear_combination
      (-4 * A ^ 2 * S.a4 - 192 * B ^ 2) * he4 +
        (48 * A * B) * he3
  have hr5clear :
      1024 * GCD369CubeFaberR5
          S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 * A ^ 3 -
        A ^ 4 * (A * w - 4 * B ^ 2) = 0 := by
    rw [hr5compact]
    linear_combination
      (-A ^ 4 / 2 + A ^ 3 * S.a4 ^ 2 / 3) * he4 -
        (2 * A ^ 3 * S.a3) * he3
  have hr5cancelled :
      1024 * GCD369CubeFaberR5
          S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 * A -
        A ^ 2 * (A * w - 4 * B ^ 2) = 0 := by
    have hfactor : A ^ 2 *
        (1024 * GCD369CubeFaberR5
            S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 * A -
          A ^ 2 * (A * w - 4 * B ^ 2)) = 0 := by
      linear_combination hr5clear
    exact (mul_eq_zero.mp hfactor).resolve_left (pow_ne_zero 2 hA)
  have hAV : A * V = A * w + 8 * B ^ 2 := by
    dsimp only [V]
    field_simp [hA]
  have hr5final :
      1024 * GCD369CubeFaberR5
          S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 -
        A * (A * w - 4 * B ^ 2) = 0 := by
    have hfactor : A *
        (1024 * GCD369CubeFaberR5
            S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 -
          A * (A * w - 4 * B ^ 2)) = 0 := by
      linear_combination hr5cancelled
    exact (mul_eq_zero.mp hfactor).resolve_left hA
  have hr5formula :
      GCD369CubeFaberR5 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
        A * (A * V - 12 * B ^ 2) / 1024 := by
    rw [hAV]
    field_simp
    linear_combination hr5final
  exact ⟨hA, hrho4formula, hrho3formula, hr5formula⟩

set_option maxHeartbeats 4000000 in
/-- When `rho4` vanishes, the same exact Faber source automatically lies on
one of the two unmixed reduced sheets: the zero-bracket sheet or the elliptic
sheet.  This is the complementary, non-localized part of the later-fibre
handoff. -/
theorem unmixedCoordinates {K : Type u} [Field K] [CharZero K]
    (S : GCD369CubeLaterInvariantSource K) (hrho4 : S.rho4 = 0) :
    let A := 4 * S.a2 - S.a4 ^ 2
    let B := 2 * S.a1 - S.a3 * S.a4
    let w := 4 * S.a0 - S.a3 ^ 2
    (A = 0 ∧ B = 0 ∧ 9 * w ^ 2 - 384 * S.rho3 = 0) ∨
      (S.a3 = 0 ∧ S.a1 = 0 ∧
        384 * S.a2 ^ 3 - 432 * S.a2 ^ 2 * S.a4 ^ 2 +
            144 * S.a2 * S.a4 ^ 4 - 15 * S.a4 ^ 6 +
            6144 * S.rho3 = 0 ∧
        48 * S.a0 - 12 * S.a2 * S.a4 + 3 * S.a4 ^ 3 = 0) := by
  dsimp only
  let e4 : K :=
    64 * S.a0 * S.a2 - 16 * S.a0 * S.a4 ^ 2 + 32 * S.a1 ^ 2 -
      32 * S.a1 * S.a3 * S.a4 - 16 * S.a2 ^ 2 * S.a4 -
      16 * S.a2 * S.a3 ^ 2 + 8 * S.a2 * S.a4 ^ 3 +
      12 * S.a3 ^ 2 * S.a4 ^ 2 - S.a4 ^ 5
  let e3 : K :=
    64 * S.a0 * S.a1 - 32 * S.a0 * S.a3 * S.a4 -
      32 * S.a1 * S.a2 * S.a4 - 16 * S.a1 * S.a3 ^ 2 +
      8 * S.a1 * S.a4 ^ 3 - 16 * S.a2 ^ 2 * S.a3 +
      24 * S.a2 * S.a3 * S.a4 ^ 2 + 8 * S.a3 ^ 3 * S.a4 -
      5 * S.a3 * S.a4 ^ 4
  let p2 : K :=
    1152 * S.a0 ^ 2 - 768 * S.a0 * S.a2 * S.a4 -
      576 * S.a0 * S.a3 ^ 2 + 192 * S.a0 * S.a4 ^ 3 -
      384 * S.a1 ^ 2 * S.a4 - 1152 * S.a1 * S.a2 * S.a3 +
      672 * S.a1 * S.a3 * S.a4 ^ 2 - 192 * S.a2 ^ 3 +
      336 * S.a2 ^ 2 * S.a4 ^ 2 + 768 * S.a2 * S.a3 ^ 2 * S.a4 -
      132 * S.a2 * S.a4 ^ 4 + 72 * S.a3 ^ 4 -
      288 * S.a3 ^ 2 * S.a4 ^ 3 + 15 * S.a4 ^ 6 -
      3072 * S.rho3
  let p1 : K :=
    96 * S.a0 * S.a1 * S.a4 + 192 * S.a0 * S.a2 * S.a3 -
      96 * S.a0 * S.a3 * S.a4 ^ 2 + 96 * S.a1 ^ 2 * S.a3 +
      144 * S.a1 * S.a2 ^ 2 - 120 * S.a1 * S.a2 * S.a4 ^ 2 -
      120 * S.a1 * S.a3 ^ 2 * S.a4 + 21 * S.a1 * S.a4 ^ 4 -
      144 * S.a2 ^ 2 * S.a3 * S.a4 - 48 * S.a2 * S.a3 ^ 3 +
      96 * S.a2 * S.a3 * S.a4 ^ 3 + 48 * S.a3 ^ 3 * S.a4 ^ 2 -
      15 * S.a3 * S.a4 ^ 5
  have he4 : e4 = 0 := by
    have hscale :
        GCD369CubeFaberR1 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
          (3 / 256 : K) * e4 := by
      dsimp [e4, GCD369CubeFaberR1]
      ring
    have hr1 := S.hr1
    rw [hscale] at hr1
    exact (mul_eq_zero.mp hr1).resolve_left (by norm_num)
  have he3 : e3 = 0 := by
    have hscale :
        GCD369CubeFaberR2 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
          (3 / 256 : K) * e3 := by
      dsimp [e3, GCD369CubeFaberR2]
      ring
    have hr2 := S.hr2
    rw [hscale] at hr2
    exact (mul_eq_zero.mp hr2).resolve_left (by norm_num)
  have hp2 : p2 = 0 := by
    have hscale :
        GCD369CubeFaberR3 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
          (p2 + 3072 * S.rho3) / 3072 := by
      dsimp [p2, GCD369CubeFaberR3]
      ring
    have hr3 := S.hr3
    rw [hscale] at hr3
    linear_combination 3072 * hr3
  have hp1 : p1 = 0 := by
    have hscale :
        GCD369CubeFaberR4 S.a0 S.a1 S.a2 S.a3 S.a4 0 0 0 0 0 0 0 =
          -p1 / 768 := by
      dsimp [p1, GCD369CubeFaberR4]
      ring
    have hr4 := S.hr4
    rw [hscale, hrho4] at hr4
    have hp1scaled : (-1 / 768 : K) * p1 = 0 := by
      simpa [div_eq_mul_inv] using hr4
    exact (mul_eq_zero.mp hp1scaled).resolve_left (by norm_num)
  by_cases hA : 4 * S.a2 - S.a4 ^ 2 = 0
  · left
    have hBsq : 24 * (2 * S.a1 - S.a3 * S.a4) ^ 2 = 0 := by
      dsimp [e4] at he4
      linear_combination 3 * he4 -
        (3 * S.a4 ^ 3 - 12 * S.a3 ^ 2 - 12 * S.a2 * S.a4 +
          48 * S.a0) * hA
    have hB : 2 * S.a1 - S.a3 * S.a4 = 0 := by
      have h24 : (24 : K) ≠ 0 := by norm_num
      exact (pow_eq_zero_iff (by norm_num : (2 : Nat) ≠ 0)).mp
        ((mul_eq_zero.mp hBsq).resolve_left h24)
    refine ⟨hA, hB, ?_⟩
    dsimp [p2] at hp2
    linear_combination
      (1 / 8) * hp2 -
      (1 / 8) * (-15 * S.a4 ^ 4 + 288 * S.a3 ^ 2 * S.a4 +
        72 * S.a2 * S.a4 ^ 2 - 48 * S.a2 ^ 2 -
        480 * S.a1 * S.a3 - 192 * S.a0 * S.a4) * hA -
      (1 / 8) * (384 * S.a2 * S.a3 - 192 * S.a1 * S.a4) * hB
  · right
    dsimp [e4] at he4
    dsimp [e3] at he3
    dsimp [p1] at hp1
    have hsplit : S.a3 * (4 * S.a2 - S.a4 ^ 2) ^ 4 = 0 := by
      linear_combination
        (-8 / 3 * S.a3 * S.a4 ^ 3 + 16 / 3 * S.a3 ^ 3 +
          32 / 3 * S.a2 * S.a3 * S.a4 - 64 / 3 * S.a0 * S.a3) * he4 +
        (-7 / 3 * S.a4 ^ 4 + 8 / 3 * S.a3 ^ 2 * S.a4 +
          40 / 3 * S.a2 * S.a4 ^ 2 - 16 * S.a2 ^ 2 -
          32 / 3 * S.a0 * S.a4) * he3 +
        (8 / 9 * S.a4 ^ 3 - 16 / 9 * S.a3 ^ 2 -
          32 / 9 * S.a2 * S.a4 + 64 / 9 * S.a0) * hp1
    have ha3 : S.a3 = 0 := by
      rcases mul_eq_zero.mp hsplit with h | h
      · exact h
      · exact False.elim ((pow_ne_zero 4 hA) h)
    have haux :
        2 * S.a1 * (4 * S.a2 - S.a4 ^ 2) ^ 2 +
          S.a3 * (-16 * S.a2 ^ 2 * S.a4 + 8 * S.a2 * S.a4 ^ 3 -
            S.a4 ^ 5) = 0 := by
      linear_combination (-2 / 3 * S.a3) * he4 +
        (-1 / 3 * S.a4) * he3 + (2 / 9) * hp1
    have ha1 : S.a1 = 0 := by
      rw [ha3, zero_mul, add_zero] at haux
      have h2 : (2 : K) ≠ 0 := by norm_num
      rcases mul_eq_zero.mp haux with h | h
      · exact (mul_eq_zero.mp h).resolve_left h2
      · exact False.elim ((pow_ne_zero 2 hA) h)
    refine ⟨ha3, ha1, ?_, ?_⟩
    · have hlin :
          48 * S.a0 - 12 * S.a2 * S.a4 + 3 * S.a4 ^ 3 = 0 := by
        have hprod :
            (4 * S.a2 - S.a4 ^ 2) *
              (48 * S.a0 - 12 * S.a2 * S.a4 + 3 * S.a4 ^ 3) = 0 := by
          linear_combination 3 * he4 -
            (36 * S.a3 * S.a4 ^ 2 - 48 * S.a2 * S.a3 -
              96 * S.a1 * S.a4) * ha3 - (96 * S.a1) * ha1
        exact (mul_eq_zero.mp hprod).resolve_left hA
      dsimp [p2] at hp2
      linear_combination
        (-2) * hp2 +
        2 * (5 / 2 * S.a4 ^ 3 - 10 * S.a2 * S.a4 + 24 * S.a0) * hlin +
        2 * (-288 * S.a3 * S.a4 ^ 3 + 72 * S.a3 ^ 3 +
          768 * S.a2 * S.a3 * S.a4 + 672 * S.a1 * S.a4 ^ 2 -
          1152 * S.a1 * S.a2 - 576 * S.a0 * S.a3) * ha3 -
        (768 * S.a1 * S.a4) * ha1
    · have hprod :
          (4 * S.a2 - S.a4 ^ 2) *
            (48 * S.a0 - 12 * S.a2 * S.a4 + 3 * S.a4 ^ 3) = 0 := by
        linear_combination 3 * he4 -
          (36 * S.a3 * S.a4 ^ 2 - 48 * S.a2 * S.a3 -
            96 * S.a1 * S.a4) * ha3 - (96 * S.a1) * ha1
      exact (mul_eq_zero.mp hprod).resolve_left hA

end GCD369CubeLaterInvariantSource

#print axioms GCD369CubeLeadingFaberSource.toComponent
#print axioms GCD369CubeEarlyFaberJetSource.toArbitraryLoad_or_allZero
#print axioms GCD369CubeEarlyFaberBoundarySource.empty
#print axioms GCD369CubeLaterInvariantSource.mixedCoordinates
#print axioms GCD369CubeLaterInvariantSource.unmixedCoordinates
