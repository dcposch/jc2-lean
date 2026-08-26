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

#print axioms GCD369CubeLeadingFaberSource.toComponent
#print axioms GCD369CubeEarlyFaberJetSource.toArbitraryLoad_or_allZero
#print axioms GCD369CubeEarlyFaberBoundarySource.empty
