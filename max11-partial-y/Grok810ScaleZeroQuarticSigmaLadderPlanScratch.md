# (8,10) scale-zero, cone `A`: Stage-B plan (σ-defect ladder + 63 argmin cones) — Opus, 2026-09-04

All coefficients below were read out of the checked-in CAS transcription
`scripts/out_810_scale_zero_quartic_coordinates.json` (produced by
`derive_810_scale_zero_quartic_coordinates.py` from the Lean text, isobaric-verified) and
cross-checked against `Grok810ScaleZeroQuarticDefsScratch.lean`. Every new numeric claim in §2
(the auxiliary `N₂`, its columns, the five 2×2 determinants) was recomputed from that transcription.

Template method: `Grok610ScaleZeroCubicLoadCompetePlanScratch.md` (whole file).

---

## 0. Where the leaf actually stands

`normalized810ScaleZero_quarticADominantResidual` (`Grok810ScaleZeroQuarticConesScratch.lean:46067`)
hands over the seven-integral packet in quartic letters plus `QuarticRatioConeA810 ∨ QuarticRatioConeABCDEFG810`
(`Grok810ScaleZeroQuarticDefsScratch.lean:1306`, `:2881`). `quarticConeA810_residual`
(`Grok810ScaleZeroQuarticADominantScratch.lean:1203`) closes only the all-constant cell with `l/β/δ/ζ` live
and even-core `{C}`,`{E}`. Its docstring records the two facts that dictate this plan:

* **`grading.min_sigma = 2` for all seven integrals** — every load-free monomial has **at least two** letters from `B…G`;
* **`matrix.rank = 0`** — the quartic substitution killed *every* one-letter face, so the original plan's §5 B1 (the `4×3` odd matrix) is dead. §3 below.

---

## 1. The σ-defect grading — verified

### 1.1 Defects and the cone

With `a := A.natDegree, …, g := G.natDegree`, `ρ := a/2`, `σ_X := w_X ρ − n_X`, weights `w_{A..G} = 2,3,4,5,6,7,8`. Doubled, division-free:

```
s_B = 3a − 2b   s_C = 4a − 2c   s_D = 5a − 2d
s_E = 6a − 2e   s_F = 7a − 2f   s_G = 8a − 2g          (s_X = 2σ_X)
```

`QuarticRatioConeA810` (`…QuarticDefsScratch.lean:1306`) is exactly `s_X > 0` for all six letters plus `0 < a`.
Put `s := min{s_X : X ≠ 0}` (so `0 < s ≤ 8a`, and `s ≤ 3a` whenever `B ≠ 0`).

Degree of a monomial with load `π` (weight `w_π`), `A`-power `i`, letters `m`:

```
2·deg = (w − w_π)·a − Σ_X m_X s_X                      (w = weight of the integral)
```

So a load-free monomial sits at `2·deg = w·a − cost`, `cost := Σ m_X s_X ≥ 2s` (by `min_sigma = 2`),
and a pure-`A` load column sits at `2·deg = (w − w_π)a`.

### 1.2 The σ-2 letter faces

Writing `S₁₁ := BG + CF + DE`, `S₁₃ := DG + EF`, `S₁₅ := FG`:

| Φ | w | σ-2 part | Lean lines (`…QuarticDefsScratch.lean`) |
|---|---|---|---|
| `κ` | 11 | `(5/16)·S₁₁` | `133,134,135` |
| `μ` | 12 | `−(5/64)ABF − (5/128)AD² + (5/16)CG + (5/16)DF + (5/32)E²` | `173,174,178,179,180` |
| `ν` | 13 | `−(5/128)A·S₁₁ + (5/16)S₁₃` | `224–226, 231–232` |
| `ξ` | 14 | `−(5/64)ADF + (5/16)EG + (5/32)F²` | `290, 296, 297` |
| `ο` | 15 | `−(5/2048)A²S₁₁ − (5/128)A·S₁₃ + (5/16)S₁₅` | `357–359, 367–368, 375` |
| `π` | 16 | `−(5/16)AF² + (5/4)G²` | `472, 479` |
| `Π` | 17 | `−(5/2048)A³S₁₁ − (5/256)A²S₁₃ − (5/16)A·S₁₅` | `612–614, 624–625, 637` (`rhoBaseGroupQuartic810`, `:605`) |

Complete list of 2-letter supports occurring anywhere: `{BF, BG, CF, CG, D², DE, DF, DG, E², EF, EG, F², FG, G²}` —
`BB, BC, BD, BE, CC, CD, CE` are **absent**. Consequence:

> `min_sigma(S) = 3` **exactly** for `S ∈ {{B},{C},{B,C}}` (faces `B³, C³, B²C, BC²`); `min_sigma(S) = 2` for the other 60 subsets.

Parity: `B,D,F,l,β,δ,ζ,θ` odd; `A,C,E,G,γ,ε,η` even; `κ,ν,ο,Π` odd, `μ,ξ,π` even.

### 1.3 Pure-`A` load columns

| Φ | `l` | `β` | `δ` | `ζ` | `θ` |
|---|---|---|---|---|---|
| `κ` | `63/262144·A⁵` | `35/32768·A⁴` | `5/1024·A³` | `3/128·A²` | `1/8·A` |
| `ν` | `105/4194304·A⁶` | `7/65536·A⁵` | `15/32768·A⁴` | `1/512·A³` | `1/128·A²` |
| `ο` | `135/33554432·A⁷` | `35/2097152·A⁶` | `9/131072·A⁵` | `9/32768·A⁴` | `1/1024·A³` |
| `Π` | `1575/268435456·A⁸` | `25/1048576·A⁷` | `25/262144·A⁶` | `3/8192·A⁵` | `5/4096·A⁴` |
| `μ, ξ, π` | — | — | — | — | — |

**`μ, ξ, π` have no pure-`A` column whatsoever** (the `(6,10)` `λ/ο` analogues), and `γ, ε, η` have no pure-`A` column in *any* integral.

### 1.4 The load-letter *shadow* principle

For every load `π'` with a same-weight letter (`β/B`, `γ/C`, `δ/D`, `ε/E`, `ζ/F`, `η/G`), each monomial `π'·m` of `Φ` mostly has its shadow `X·m` in the load-free part:
* `γ/C`, `ε/E`, `η/G`: complete for `κ, μ, ν, ξ, ο, π`; for `Π` a single exception, `γ·A·C·F`.
* `β/B`, `δ/D`, `ζ/F`: complete except a tiny residue of low-letter-count monomials (e.g. `κ`: `β{A⁴, A²C, AE}`, `δ{A³, AC}`, `ζ{A²}`; `μ`: `β{A³B, A²D}`, `δ{A²B}`).
* **`l` and `θ` have no shadow letter.**

Since `deg(π'·m) = deg(X·m) − n_X`, a shadowed column is strictly below the load-free part whenever `n_X ≥ 1`.

---

## 2. Auxiliaries, kill predicates, and why there are (almost) no tie chambers

### 2.1 Killing a load

For a carrier `Φ` (weight `w`) with a pure-`A` `π`-column and load-free minimal cost `c₀`: the π-column strictly tops Φ ⇔ `c₀ > w_π·a` (doubled units), then `natDegree Φ ≥ (w−w_π)a/2 ≥ 4a`, contradicting `natDegree Φ = 0` (or `natDegree Π = 1 ≤ 3a`). Dually, on cone `S` with `k := min_sigma(S)` and carrier `Φ`, a load column with minimal letter count `ℓ` fails to beat the `k·s` face iff `w_π·a + ℓ·s > k·s`.

### 2.2 `k = 2` cones (60 of 63): **`κ` alone runs the whole ladder — no auxiliary**

| load | `κ` kills it iff | even carrier `μ/ξ/π` (`ℓ = 1`) tops it iff | union |
|---|---|---|---|
| `l` (1) | `2s > a` | `a > s` | exhaustive, overlap `(a/2, a)` |
| `β` (3) | `2s > 3a` | `3a > s` | overlap `(3a/2, 3a)` |
| `δ` (5) | `2s > 5a` | `5a > s` | overlap |
| `ζ` (7) | `2s > 7a` | `7a > s` | overlap |
| `θ` (9) | `2s > 9a` | `9a > s` — **always true** (`s ≤ 8a`) | never needed |
| `γ` (4) | *unkillable* | `4a > s` | **fails iff `s ≥ 4a`** |
| `ε` (6) | *unkillable* | `6a > s` | fails iff `s ≥ 6a` |
| `η` (8) | *unkillable* | `8a > s` | fails iff `s = 8a` |

Every union is strict: **no tie chambers**; `θ` needs no auxiliary because `κ` is quadratic in the letters. Ladder order `l → β → δ → ζ` is forced.

### 2.3 `k = 3` cones (`S ∈ {{B},{C},{B,C}}`): the auxiliary `N₂`

Here `κ`'s band is `w_π a > 3s` (S = {B}) or `w_π a > 2s` (S = {C},{B,C}, `μ` available), while `κ`'s kill is `2s > w_π a` — a genuine tie at `2s = w_π a`. Fix:

```lean
/-- ν + (1/8)·A·κ : weight 13, level-2 face (5/16)(DG+EF), zero on S ⊆ {B,C}. -/
def degreeZeroN2Quartic810 (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroNuQuartic810   l beta gamma delta epsilon zeta eta theta A B C D E F G
  + (1/8 : k) • (A * degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
                        A B C D E F G)
```

Computed from the transcription (56 monomials):
* load-free part is only 8 monomials: `(5/16)DG, (5/16)EF, (15/512)AB²D, −(15/128)B²F, −(15/64)BCE, −(15/128)BD², −(15/128)C²D, (35/512)B³C`. The whole `{B,C}` level-3 face cancels, leaving `B³C` at level 4.
* pure-`A` columns all survive: `l : 231/4194304·A⁶`, `β : 63/262144·A⁵`, `δ : 35/32768·A⁴`, `ζ : 5/1024·A³`, `θ : 3/128·A²` (the five 2×2 determinants `c_ν + c_κ/8`, all nonzero).
* `γ`-column has letter count ≥ 2; `ε` is `F`, `η` is `D`.
* `natDegree N₂ ≤ a`, from `natDegree κ = natDegree ν = 0` (`natDegree_mul_le` + `natDegree_smul_le810`, `Grok810ScaleZeroConeEliminationScratch.lean:92`).

With the §2.5 sub-chamber conjuncts, `c₀(N₂) > (7/2)s`, hence `N₂` kills π ⇐ `7·s ≥ 2·w_π·a`:

| load | `N₂` kill | `κ`/`μ` face-top on `S={B}` / `S={C},{B,C}` | union |
|---|---|---|---|
| `l` | `7s ≥ 2a` | `a > 3s` / `a > 2s` | strict, exhaustive |
| `β` | `7s ≥ 6a` | `3a > 3s` / `3a > 2s` | strict |
| `δ` | `7s ≥ 10a` | `5a > 3s` / `5a > 2s` | strict |
| `ζ` | `7s ≥ 14a` | `7a > 3s` / `7a > 2s` | strict |
| `θ` | `7s ≥ 18a` | `9a > 3s` / `9a > 2s` | strict |

(`7s < 2w_π a ∧ w_π a ≤ 3s ⟹ 6s ≥ 2w_π a > 7s`, impossible.) **No tie chambers, no wall file.** The `θ`/`B³` tie on `A⁴` the current residual leaves open is `s = 3a` on `S = {B}` (`b = 0`), and `21a ≥ 18a` — `N₂` kills `θ` there (cross-check: `κ`'s `A¹` gives `(5/512)b³ + θ/8 = 0`, `Π`'s `A⁴` gives `−(5/65536)b³ + (5/4096)θ = 0`, determinant `45/2097152 ≠ 0`).

### 2.4 The one genuinely open region: corner **H**, `s ≥ 4a`

`s ≥ 4a` forces `B = 0` and `C = 0` or `c = 0`; the ladder has killed `l, β, δ, ζ` and `θ`'s band holds. The obstruction is the **unkillable even loads** `γ (4a > s)`, `ε (6a > s)`, `η (8a > s)`. Remedies, in order:
1. **Change carrier.** `γ` has `ℓ = 2` in `ξ` and `π`; `ε` has `ℓ = 2` in `π`. Use `π` (only `η` binds, `8a > s`) or `ξ` (`6a > s`, `8a > s`). `π`'s level-2 face `−(5/16)AF² + (5/4)G²` is nonzero whenever `F ∈ S` or `G ∈ S`; `ξ`'s for `F ∈ S`, `{D,F} ⊆ S`, `{E,G} ⊆ S`.
2. **Residual corner:** `B = 0`, `S ⊆ {C,D,E}`, `s ≥ 4a` (`c = 0`, `2d ≤ a`, `e ≤ a`). Tools: (a) branch `γ = 0 ∨ G = 0` from "if `γ·G` strictly tops `μ` then its leading coefficient vanishes"; (b) if `D = F = 0` (and `B = 0`) with all odd loads dead, `Π ≡ 0` by parity — §4.3.
3. `s = 8a` is the `G`-only corner: `B=C=D=E=F=0`, `g = 0` ⇒ §4.3.

### 2.5 The sub-chamber correction to the existing `QuarticSigmaCone*810`

**Correctness gap in the current definitions; fix before any rest bound.** `QuarticSigmaConeB810` (`…QuarticADominantScratch.lean:54`) and its `C`, `BC` siblings are raw σ-argmin cones. For `k = 3` cones 2-letter monomials `BG, BF, CG, CF, D², …` may have cost `< 3σ_B`. Add, cross-multiplied:

```lean
-- S = {B}:  2σ_B < σ_F,  2σ_B < σ_G,  3σ_B < 2σ_D,  3σ_B < 2σ_E
    ∧ 2 * F.natDegree < A.natDegree + 4 * B.natDegree      -- 2σ_B < σ_F
    ∧ G.natDegree < A.natDegree + 2 * B.natDegree          -- 2σ_B < σ_G
    ∧ 4 * D.natDegree < A.natDegree + 6 * B.natDegree      -- 3σ_B < 2σ_D
    ∧ 4 * E.natDegree < 3 * A.natDegree + 6 * B.natDegree  -- 3σ_B < 2σ_E
```
(`C`-analogues `2f < 3a + 4c`, `g < 2c`, `4d < 3a + 6c`, `4e < 6a + 6c`; `S = {B,C}` takes `σ_B = σ_C` plus the same four.) The complements inside these `S` are covered by `k = 2` cones with a different support (`{B,G}`, `{C,F}`, `{D}`, …) and the same face/rest defs — extra cone constructors in the exhaust, no new certificates.

---

## 3. B1 (odd letters): rank **0** — replaced by the 63 argmin certificates

`matrix.rank = 0` (`out_810_scale_zero_quartic_adominant.json`, `matrix.entries`): every partial is quadratic in the letters. Do not attempt `quarticADominant_oddLetters_eq_zero`. The 63 argmin cones all have `status = "one"`:
* **9 single-monomial** kills: `C`(`μ:c³`), `D`(`μ:ad²`), `E`(`μ:e²`), `BD`, `BE`, `CD`, `CE`, `BCD`, `BCE` — all `μ`.
* **~30 one-carrier, one-monomial** kills: `F, BF, CF, BCF, BCEF, BCDF*` → `ξ:f²`; `G, BG, CG, DG, BCG, BDG, CDG, BCDG, CEG, BCEG, CDEG, BCDEG, DEG, BDEG` → `π:g²`; `EF, EG, BEG, CEF, EFG` → `μ:e²`; `FG, BFG, CFG` → `ξ:f²`.
* **`B`**: `κ` restricted is `5·A·B³/512` — a single monomial.
* **~20 genuine multi-integral `linear_combination`s**, cofactors in `b1[*].combo.hs`, e.g. `BC : c⁵ = −(9abc/640)·κ_face + (3ab²/640 − c²/20)·μ_face`; `DE : e³ = (ad/20)·κ_face + (e/20)·μ_face`; `DF : f³ = (af/60)·μ_face + (−ad/60 + f/10)·ξ_face`; `CEFG : g³ = (3a³f/2560)·κ + (a²f/1280)·ν + (af/2560)·ο + (g/20)·π`; `BCDEFG : f³ = (−3a²e/160 + ag/20)·κ + (−ae/80 + g/20)·ν + (f/10)·ξ + (−e/160)·ο + (−d/10)·π`.

Only `B` and `BC` need an odd carrier; all other 61 cones have a `μ`, `ξ` or `π` carrier.

---

## 4. The even core, and the endgame

### 4.1 `μ, ξ, π` on `B = D = F = 0` are `A`-free — including all load columns

```
μ|even = −5C³/128 + 5CG/16 + 5E²/32     + γ(−3C²/32 + 3G/4) + ε(E/2)          + η(C/4)
ξ|even = −15C²E/128 + 5EG/16            + γ(−3CE/16)        + ε(−C²/8 + G/2)  + η(E/4)
π|even = 15C⁴/256 − 5C²G/16 − 5CE²/8 + 5G²/4
                                        + γ(C³/8 − 3E²/4)   + ε(−CE)          + η(−C²/4 + 2G)
```

### 4.2 The seven even cones — all closed, 2 already in Lean

| `S` | carriers | certificate |
|---|---|---|
| `{C}` | `μ` | `c³` — **done**, `quarticEvenCore_C_impossible` (`…QuarticADominantScratch.lean:247`) |
| `{E}` | `μ` | `e²` — **done**, `:279` |
| `{G}` | `π` | `g²`, one monomial `(5/4)G²` |
| `{C,E}` | `ξ` | `c²e`, one monomial `−(15/128)C²E` |
| `{E,G}` | `μ` | `e²` |
| `{C,G}` | `μ, π` | `10c⁶ = c²·π_e + c(c² − 8g)·μ_e` |
| `{C,E,G}` | `μ, ξ, π` | `c⁷ = (−c⁴/5 + 4c²g/5 + 256ce²/55 − 32g²/5)·μ_e + (4e(−17c² − 20g)/55)·ξ_e + (4cg/5 + 32e²/55)·π_e` |

After §3 the even core is a sub-case of the general exhaust; keep §4.2 as the cheap fallback for that branch.

### 4.3 B3 endgame and the two degenerate corners

* **All letters zero.** `Π = l c₁A⁸ + β c₂A⁷ + δ c₃A⁶ + ζ c₄A⁵ + θ c₅A⁴`, exponents `≥ 4a > 1`, so `natDegree Π = 1` forces `Π = 0`, contradicting `derivative Π = C (j/t) ≠ 0`. `quarticADominant_allLettersZero_impossible` — mirror `cubicADominant_allLettersZero_impossible` (`Grok610ScaleZeroCubicADominantScratch.lean:3043`).
* **Parity corner `B = D = F = 0` and `l = β = δ = ζ = θ = 0` ⇒ `Π ≡ 0`.** `Π` has odd weight 17 and `A, C, E, G, γ, ε, η` are all even. Same three-line proof as `cubicLoadCompete_BD_zero_impossible`.
* **Constant letters, `A` nonconstant, `l = β = δ = ζ = 0`** (the `θ/B³` tie): subsumed by §2.3. `degreeZeroPrimitivePolynomial810_false_of_constant_core` (`Grok810ScaleZeroConeEliminationScratch.lean:1564`) requires `A.natDegree = 0` and does not apply inside cone `A`. The `θ`-column of `Π` on the even core is `5A⁴/4096 + 3A²C/128 + AE/8 − C²/16 + G`.

---

## 5. Lean lemma sequence

Namespace `Max11DegreeRoutes`; Tier-1 perf preamble copied from `…QuarticADominantScratch.lean:37–46`.

### File A — `Grok810ScaleZeroQuarticSigmaLadderScratch.lean` (imports `Grok810ScaleZeroQuarticADominantScratch`)
1. **Fix the `k = 3` cones**: `QuarticSigmaConeB810'`, `…C810'`, `…BC810'` = existing bodies (`:54`, `:70`) plus the four cost conjuncts of §2.5, `X ≠ 0` for `X ∈ S`, and `Y = 0 ∨ strict` for `Y ∉ S` (the `(6,10)` `CubicLoadSigmaConeCD610` shape).
2. **`k = 2` cones**: 60 defs `QuarticLoadSigmaCone{D,E,F,G,BD,…,BCDEFG}810` from the CAS `nat_conjuncts` with the same edits, minus the final "`k·s < ρ`" conjunct.
3. **The exhaust** `quarticSigmaSupportCone810_of`, modelled on `cubicSigmaSupportCone610_of` (`Grok610ScaleZeroCubicWallScratch.lean:866`): `by_cases hX : X = 0` for the six letters (64 leaves), then the 15 pairwise σ comparisons; all-zero leaf → `quarticADominant_allLettersZero_impossible`. Split 64-ways first (~1500 lines).
4. **`N₂`**: def, `degreeZeroN2Quartic810_natDegree_le`, faces `n2QuarticLFace810 := (231/4194304 * l) • A^6`, `Beta (63/262144)•A^5`, `Delta (35/32768)•A^4`, `Zeta (5/1024)•A^3`, `Theta (3/128)•A^2`, `degreeZeroN2QuarticNoL810` (55 monomials, three ~20-monomial chunks with `_natDegree_le` by `simp only; compute_degree; omega`, combined with `natDegree_add4_lt810` `…QuarticADominantScratch.lean:322` — pattern `rhoBaseLetters1Quartic810_natDegree_le` `:651`, `rhoBaseGroupQuarticNoA8810_natDegree_lt` `:835`). **Never `compute_degree` a 56-monomial body with seven symbolic degrees — that was the 94 GB OOM.**
5. **Kill predicates** (cross-multiplied ℕ): `QuarticKappaLoadTop810 (w)` = `2s > w·a`, `QuarticN2LoadTop810 (w)` = `7s ≥ 2w·a`, per cone with `s` expanded; kills `quarticSigma_l_eq_zero`, `…_beta_`, `…_delta_`, `…_zeta_`, `…_theta_` (θ only on the three `k = 3` cones).
6. **Corners:** `quarticADominant_allLettersZero_impossible`, `quarticParityCorner_BDF_zero_impossible`.
7. **Export** `normalized810ScaleZero_quarticSigmaResidual`: packet, cone `A`, the 63-way `QuarticSigmaSupportCone810`, per-load band disjunctions.

### File B — `Grok810ScaleZeroQuarticSigmaKillsScratch.lean`: the ~40 one-monomial cones
Per cone: face def, chunked rest def, `_eq_sigmaS_add_rest` (`simp only; all_goals module`), the rest bound with the band disjunctions as hypotheses (`rcases … <;> (simp only [def, zero_mul, …]; compute_degree; omega)`; pre-substituted per-band rest defs if the budget blows), then `quarticSigmaCone_S_impossible` via `natDegree_add_eq_left_of_natDegree_lt` + `omega`. Template: `Grok810ScaleZeroQuarticKillsScratch.lean:32/36/83/94/113`. Bands are the `¬kill` side of §2.2; `θ, γ, ε, η` need no hypothesis on `k = 2` cones except corner H.

### File C — `Grok810ScaleZeroQuarticSigmaMultiScratch.lean`: the ~20 multi-integral cones
`BC, DE, DF, BDF, CDF, DEF, DFG, CDFG, BDFG, BCDFG, BDEF, CDEF, BCDEF, BEFG, BCEFG, CEFG, DEFG, BDEFG, CDEFG, BCDEFG` with the CAS `hs` as `linear_combination`, `by_cases hI : innerForm = 0` pattern of `mu_xi_AC02_impossible` (`Grok810ScaleZeroConeExhaustionScratch.lean:2428`), `_coeff_top` lemmas as `kappaCubicSigmaFaceBC610_coeff_top` (`Grok610ScaleZeroCubicADominantScratch.lean:956`).

### File D — `Grok810ScaleZeroQuarticEvenCoreScratch.lean`: the five remaining even cones + corner H-(2)
Reuse `degreeZeroMuQuartic810_evenCore` (`…QuarticADominantScratch.lean:182`), `degreeZeroXiQuartic810_evenCore` (`:202`), new `degreeZeroPiQuartic810_evenCore`.

### File E — assembly
```lean
theorem normalized810ScaleZero_impossible {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) : False
theorem planeKeller810ScaleZeroExclusion_closed : PlaneKeller810ScaleZeroExclusion (K := K) :=
  planeKeller810ScaleZeroExclusion_of_impossible normalized810ScaleZero_impossible
```
(`Grok810ScaleZeroConeEliminationScratch.lean:2266`; the `ABCDEFG` branch comes from the sibling lane.)

### Reuse map (file:line)
* packet: `normalized810ScaleZero_quarticADominantResidual` `Grok810ScaleZeroQuarticConesScratch.lean:46067`; `quarticConeA810_residual` `Grok810ScaleZeroQuarticADominantScratch.lean:1203`
* integrals: `degreeZeroKappaQuartic810` `…QuarticDefsScratch.lean:127`, `Mu :168`, `Nu :217`, `Xi :282`, `Omicron :349`, `Pi :591` (`piBaseGroupQuartic810 :457`, groups `:509–585`), `Primitive :804` (`rhoBaseGroupQuartic810 :605`, groups `:687–793`)
* cones: `QuarticRatioConeA810 :1306`, `QuarticRatioConeABCDEFG810 :2881`; σ-cones `…QuarticADominantScratch.lean:54,70,86,102,118,134`
* face/rest/kill template: `Grok810ScaleZeroQuarticKillsScratch.lean:32,36,83,94,113`
* chunked `compute_degree`: `…QuarticADominantScratch.lean:341–532` (defs), `:651–833` (`_natDegree_le`), `:835,859,903,952,996`, helpers `:317,322`
* natDegree helpers: `Grok810ScaleZeroConeEliminationScratch.lean:68,82,87,92,99,103,107,111,128`
* closed corners: `degreeZeroPrimitivePolynomial810_false_of_constant_core :1564`; `quarticADominant_constantLetters_impossible_of_{l,beta,delta,zeta}` `…QuarticADominantScratch.lean:1037,1074,1112,1150`
* even core: `degreeZeroMuQuartic810_evenCore :182`, `degreeZeroXiQuartic810_evenCore :202`, `quarticEvenCore_{C,E}_impossible :247,:279`
* `(6,10)` templates: `Grok610ScaleZeroCubicADominantScratch.lean:46,258,274,342,378,453,457,492,503,525,3043,3255`; `Grok610ScaleZeroCubicLoadLadderScratch.lean:49,55,61,67,1238`; `Grok610ScaleZeroCubicWallScratch.lean:866,52,147,362`

---

## 6. CAS jobs to run **before** writing Lean

Extend `scripts/derive_810_scale_zero_quartic_adominant.py` (has `saturate`, `find_wh_combo`, `cone_nat_conjuncts`):
1. **`cone_nat_conjuncts` fix**: emit *cost* comparisons, not raw σ; for `S ∈ {{B},{C},{B,C}}` emit the four extra conjuncts of §2.5. Assert for every `S` and every load-free monomial `m` of every carrier: `cost(m) ≥ k_S·s` with equality iff `supp m ⊆ S` and `|m| = k_S`.
2. **`N₂` block**: assert `ν + (1/8)Aκ` has exactly the 8 load-free monomials of §2.3; pure-`A` columns `l 231/4194304, β 63/262144, δ 35/32768, ζ 5/1024, θ 3/128`; `γ` column min letter count 2, `ε` `{F}`, `η` `{D}`; the five determinants nonzero.
3. **Band emitter**: per `(S, carrier Φ, load π)` the exact list of ℕ inequalities for `omega`, cross-multiplied, no subtraction, under the `¬kill` band; **assert strictness** of every union; any non-strict pair is a wall and must be reported.
4. **Corner H enumeration**: `s ≥ 4a` (`B = 0`, `C ∈ {0, const}`) over `S ⊆ {C,D,E,F,G}`, `γ, ε, η` live, odd loads dead; per `S` report a carrier whose `γ`/`ε`/`η` columns have letter count ≥ 2, or the `γ = 0 ∨ G = 0` branch needed. **This decides whether the lane closes.**
5. **Re-enable `enumeration`** (currently `"skipped": true`): `2⁸` load subsets × `2⁶` letter-vanishing subsets × the σ grid; assert `survivors == []`.
6. Re-emit the 63 `hs` cofactors in Lean syntax (`sympy_field_to_lean` at `derive_810_scale_zero_quartic_adominant.py:487`).

---

## 7. Honest risks and fallbacks

1. **Corner H (`s ≥ 4a`, `γ/ε/η` unkillable)** is the only incomplete region. Mitigations in §2.4; if all fail, export a *named* residual `normalized810ScaleZero_quarticSigmaResidual` carrying exactly `B = 0 ∧ s ≥ 4a ∧ S ⊆ {C,D,E} ∧ γ ≠ 0` — a two-parameter chamber.
2. **The `k = 3` cone definitions in the tracked file are under-constrained** (§2.5); replace them and route the complements to the `k = 2` cones.
3. **`compute_degree` OOM** is a chunking problem: `degreeZeroMuQuarticNoB810` (46 monomials) goes through at `maxHeartbeats 32000000` (`…QuarticKillsScratch.lean:94`); `ο` (107) / `Π` (160) need the existing group split. Prefer `μ, ξ, π, κ, N₂` as carriers — never `ο`/`Π`.
4. **Certificate transcription**: the 20 multi-integral `hs` are rational in `a..g`; transcribe as integral-cofactor `linear_combination`s, cross-checked by `ring` in CAS first.
5. **`{C,E,G}`** uses a degree-4 cofactor; fallback chain `μ ⇒ c³ = 8cg + 4e²`, `ξ ⇒ e(3c² − 8g) = 0`, split on `e = 0`.
6. **Exhaustiveness in ℕ**: 63 cones × 15 comparisons + 64 vanishing leaves; the `quarticScore_*` lemma bank (`…QuarticConesScratch.lean:293–2300`) is reusable for the σ comparisons.
7. No total-degree/twice-prime theorem, no finite-root shortcut, no new axiom.
