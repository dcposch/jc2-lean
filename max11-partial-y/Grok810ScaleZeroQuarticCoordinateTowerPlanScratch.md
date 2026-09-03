# Grok810ScaleZeroQuarticCoordinateTowerPlanScratch.md (Opus plan, 2026-09-03 ~17:30Z)

**Target:** `normalized810ScaleZero_impossible : ∀ P Q H, Normalized810LeadingCoreSource P Q H 0 → False`, hence `PlaneKeller810ScaleZeroExclusion` via `planeKeller810ScaleZeroExclusion_of_impossible` (`Grok810ScaleZeroConeEliminationScratch.lean:2266`; the route predicate is `Grok810RouteAdapterScratch.lean:27`).

**Bottom line.** The six stalled lanes are enumerating in the wrong coordinates *and* with three of the seven available first integrals switched off. In the quartic (q-adic) coordinates `q = y² + A/4` — `f = q⁴ + (By+C)q² + (Dy+E)q + (Fy+G)` — **every pure power of `A` disappears from every load-free part** (verified by hand for `μ`, `ξ`, `π` and for two `Π` faces; automatic for `κ, ν, ο, Π` by weight parity). With the three unused integrals `κ` (weight 11), `ν` (13) and `π` (16) added to the packet, the leaf has **seven integrals for seven letters** — the exact overdetermined shape that made (6,10) collapse — and Stage A reduces to **127 argmax cones with one mechanical certificate each**, all empty except `R = {A}`.

Template and method: `Grok610ScaleZeroCubicCoordinateTowerPlanScratch.md`.

---

## 1. The grading (verified, not conjectured)

All seven objects are **isobaric** for

| | A | B | C₀ | D₀ | E₀ | F₀ | G₀ | l | β | γ | δ | ε | ζ | η | θ |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| weight | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 1 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |

(`A…G₀` are the coefficients of the depressed octic `y⁸ + Ay⁶ + By⁵ + C₀y⁴ + D₀y³ + E₀y² + F₀y + G₀`, `y` has weight 1; the missing load weight is 2 — `alphaResidual810 A P = P − (5/4)A`, `LowScale810ScaleTwoSecondFace.lean:360`, is zero on the normalized leaf, exactly as weight 4 is missing in (6,10)).

Total weights, with the defining Lean text checked term by term:

| object | Lean definition | weight | natDegree |
|---|---|---|---|
| `κ` | `kappaResidual810`, `Grok810ScaleZeroTenthDefectScratch.lean:91` (degree-6 row) | **11** | 0 |
| `μ` | `degreeZeroMuPolynomial810`, `Grok810ScaleZeroConeDefectFacesScratch.lean:278` | **12** | 0 |
| `ν` | `nuResidual810`, `Fable810ScaleZeroTwelfthDefectScratch.lean:86` (degree-4 row) | **13** | 0 |
| `ξ` | `degreeZeroXiPolynomial810`, `…ConeDefectFacesScratch.lean:180` | **14** | 0 |
| `ο` | `degreeZeroOmicronPolynomial810`, `…ConeDefectFacesScratch.lean:342` | **15** | 0 |
| `π` | `piResidual810`, `Sol810PiResidualScratch.lean:113` (degree-1 row; base group `:74`) | **16** | 0 |
| `Π = ρ` | `degreeZeroPrimitivePolynomial810`, `Grok810ScaleZeroConeEliminationScratch.lean:744` | **17** | 1 |

`17 = m + n − 1`, and the seven weights are the consecutive block `11 … 17`, one per letter — the same arithmetic as (6,10) (`11…15` for five letters).

**How it was checked.** Isobaricity is the transcription checksum, run by hand on the Lean text of every group:

* `ξ`: `A⁷`, `A⁴B²`, `A⁵C₀`, `l·A⁵B`, `β·A⁴B`, `γ·A⁵`, `δ·A³B`, `ε·A⁴`, `ζ·A²B`, `η·A³`, `θ·AB`, `F₀²`, `E₀G₀`, `ε·G₀`, `ζ·F₀`, `η·E₀`, `θ·D₀` — all 14.
* `μ`: `A⁶ … B⁴ … C₀³ … E₀² … D₀F₀ … C₀G₀ … γ·G₀ … θ·B` — all 12.
* `ο`: `A⁶B`, `l·A⁷`, `B⁵`, `D₀³`, `β·A⁶`, `ζ·A⁴`, `F₀G₀`, `θ·E₀` — all 15.
* `Π`: base group `A⁷B`, `l·A⁸`, `A⁴B³`, `l·C₀⁴`, `AD₀³`, `l·G₀²` = 17; `β·A⁷`, `γ·A⁵B`, `δ·A⁶`, `ε·A⁴B`, `ζ·A⁵`, `η·A³B`, `θ·A⁴` = 17 (`rhoBetaGroupPolynomial810` … `rhoThetaGroupPolynomial810`, `…ConeEliminationScratch.lean:168–272`).
* `κ`: `L·A⁵`, `BA⁴`, `D₀E₀`, `G₀B`, `θ·A` (as `W₀·A`), `β·G₀`, `γ·F₀` = 11.
* `ν`: `L·A⁶`, `A⁵B`, `D₀G₀`, `E₀F₀`, `δ·G₀`, `θ·C₀` = 13.
* `π`: `A⁸`, `l·A⁶B`, `C₀⁴`, `G₀²`, `l·D₀³`, `θ·F₀` (via `piThetaGroup810`, `Sol810PiResidualScratch.lean:71`) = 16.

**Parity corollary (free, and load-bearing).** Parity = weight mod 2. `B, D₀, F₀` and the loads `l, β, δ, ζ, θ` are odd; `A, C₀, E₀, G₀` and `γ, ε, η` are even. Hence **`μ, ξ, π` are even and `κ, ν, ο, Π` are odd**: every monomial of an odd integral contains an odd number of `B, D, F` factors. This is what makes Stage B/C uniform (§5).

**Not usable (record it so nobody re-derives it).** `iotaResidual810` (`Grok810ScaleZeroNinthDefectScratch.lean:104`, degree-7 row) is isobaric of weight 10, but it is `X₀ − (…)` where `X₀ = b₀` is a *free* decic coefficient: it fixes `X₀` rather than constraining the letters. Its bracket has a **nonzero** pure-`A` face `(1/1024)A⁵` in the quartic coordinates, i.e. it is not a member of the weight-11…17 family. Do not put it in the packet.

### The top-form lemma

Put `n_ξ := ξ.natDegree`, `ρ := max(n_A/2, n_B/3, n_C/4, n_D/5, n_E/6, n_F/7, n_G/8)` and `R := argmax`. For an isobaric `Φ_w` the `u`-degree of a monomial `m` is `Σ m_ξ n_ξ = Σ m_ξ w_ξ (n_ξ/w_ξ) ≤ wρ`, **with equality iff `supp m ⊆ R`**; a load monomial `π·m` (`w_π ≥ 1`) sits at `≤ (w − w_π)ρ`.

> **Top-form lemma (8,10).** If `Φ_w^R ≠ 0` (the load-free part with every letter outside `R` set to `0`), then `natDegree Φ_w = wρ` and `coeff (wρ) Φ_w = Φ_w^R(lc)`.

`κ, μ, ν, ξ, ο, π` have `natDegree = 0`; `Π` has `natDegree = 1` (`natDegree_eq_one_of_derivative_eq_nonzero_C810`, `…ConeEliminationScratch.lean:68`, from `derivative Π = C (j/t) ≠ 0`). Since some letter is nonconstant (the all-constant chamber is already closed by `degreeZeroPrimitivePolynomial810_false_of_constant_core`, `…ConeEliminationScratch.lean:1564`), `ρ ≥ 1/8`, so `11ρ ≥ 11/8 > 1 ≥ natDegree Φ` for every one of the seven. **Every top form is forced to vanish; no drop chamber can occur.** This single lemma replaces every `…_natDegree_eq_of_coeff_ne` tie argument in the current chain (e.g. `xiAC02Combined810_natDegree_eq_of_coeff_ne`, used at `Grok810ScaleZeroConeExhaustionScratch.lean:2428`).

## 2. The coordinate change: `q = y² + A/4`

The right expansion is the **quartic power of the quadratic**, `f = q⁴ + (By+C)q² + (Dy+E)q + (Fy+G)` with `q = y² + A/4` — the exact analogue of (6,10)'s `f = q³ + (By+C)q + (Dy+E)`, `q = y² + A/3`. (`q⁴ = y⁸ + Ay⁶ + (3/8)A²y⁴ + (1/16)A³y² + A⁴/256`.) Explicitly, with `a := A/4`:

```
C := C0 − (3/8)A²
D := D0 − (1/2)A B
E := E0 − (1/2)A C0 + (1/8)A³
F := F0 − (1/4)A D0 + (1/16)A² B
G := G0 − (1/4)A E0 + (1/16)A² C0 − (3/256)A⁴
```

inverse (this is the direction the Lean transport lemmas use — substitute and `ring`):

```
C0 = C + (3/8)A²
D0 = D + (1/2)A B
E0 = E + (1/2)A C + (1/16)A³            ( = E + 2aC + 4a³ )
F0 = F + (1/4)A D + (1/16)A² B          ( = F + aD + a²B )
G0 = G + (1/4)A E + (1/16)A² C + (1/256)A⁴   ( = G + aE + a²C + a⁴ )
```

Graded triangular, weight preserving, so §1 applies verbatim.

**Why this one and no other (hand-verified).** Setting `B=C=D=E=F=G=0` gives `f = q⁴`, the total degeneration. The pure-`A` face of every *even* load-free part at that point cancels exactly:

* `μ₀`: `385 − 1155 + 945 + 280 − 135 − 360 − 30 + 40 + 30 = 0` (units `1/65536`) ⇒ **no `A⁶`**.
* `ξ₀`: `−330 + 1155 − 1260 − 245 + 405 + 450 + 20 − 135 − 40 − 30 + 10 = 0` (units `1/131072`) ⇒ **no `A⁷`**.
* `π₀` (from `piBaseGroup810`): `5775 − 23100 + 5040 + 30870 − 300 − 12000 − 14580 + 600 + 1280 + 6480 − 160 + 1215 − 180 − 960 + 20 = 0` ⇒ **no `A⁸`**.

`κ, ν, ο, Π` have odd weight, so a pure power of the even letter `A` cannot occur at all. Two further hand checks that matter in Stage B: the `A⁷B` and `A⁶D` coefficients of `Π₀` both vanish (sums `0` over `1/1048576` and `1/131072`), while `κ₀`'s `A⁴B` coefficient is `−5/2048 ≠ 0`.

Three more confirmations in the new letters (also Stage-A data for the `A`-cones):

```
μ₀ :  A⁴C = A²C² = A³E = A²G = A³B² = A²BD = ACE = 0 ,  AB²C = 15/512  (μ₀ is not A-free, only A-degenerate on faces)
ξ₀ :  A⁵C = A³C² = AC³ = A³G = 0 ,   A⁴B² = 45/4096 ,  AB⁴ = −15/2048
π₀ :  A⁴G = 0 ,  ∂π₀/∂G |_{B=C=D=E=F=0} = (5/2)G
```

## 3. Stage A — the 127 argmax cones

For `R` **not containing `A`** the substitution is the identity, so the restricted forms are literally the `A = 0` parts of the Lean definitions. All seven transcribed by hand (these are the CAS checksum):

```
κ₀|₀ = (5/128)( −3BC² − 3B²D + 5DE + 5CF + 5BG )
μ₀|₀ = (5/2048)( 7B⁴ − 16C³ − 96BCD − 48B²E + 64E² + 128DF + 128CG )
ν₀|₀ = (5/512)( 7B³C − 12B²F − 24BCE − 12BD² − 12C²D + 32DG + 32EF )
ξ₀|₀ = (5/1024)( 18B²C² + 11B³D − 24CD² − 24C²E − 40BDE − 40BCF − 16B²G + 32F² + 64EG )
ο₀|₀ = (1/4096)( −21B⁵ + 180BC³ + 540B²CD + 160B³E − 160D³ − 800CDE − 400C²F
                 − 400BE² − 640BDF − 600BCG + 1280FG )
π₀|₀ = (5/256)( −7B⁴C + 10B³F + 36B²CE + 18B²D² + 36BC²D − 32BDG − 48BEF
                + 3C⁴ − 16C²G − 48CDF − 32CE² − 32D²E + 64G² )
Π₀|₀ = (5/2048)( −53B³C² − 25B⁴D + 24C³D + 72BCD² + 72BC²E + 68B²DE + 68B²CF + 12B³G
                 − 128DE² − 128D²F − 256CEF − 128CDG − 128BF² − 128BEG )
```

**Singles (6 + `{A}`), all single monomials except `{A}`:**

| R | certificate | R | certificate |
|---|---|---|---|
| `B` | `μ`: `b⁴ = 0` | `C` | `μ`: `c³ = 0` |
| `D` | `ο`: `d³ = 0` | `E` | `μ`: `e² = 0` |
| `F` | `ξ`: `f² = 0` | `G` | **`π`: `g² = 0`** |
| `A` | *defect cone → Stage B* | | |

`{G}` is the single cone that has blocked three of the six stalled lanes ("unique-`G₀` degree-one chambers"): `⟨8⟩` misses `11,12,13,14,15,17`, so `κ…ο, Π` say nothing there — **`π` is exactly the missing weight `16 = 2·8` and kills it with one monomial.**

**Pairs (15 in `{B..G}`), 13 single monomials + 2 certificates:**

`BC`→`κ:bc²`, `BD`→`κ:b²d`, `BF`→`μ:b⁴`, `BG`→`μ:b⁴`, `CD`→`μ:c³`, `CE`→`ξ:c²e`, `CF`→`κ:cf`, `DE`→`κ:de`, `DF`→`μ:df`, `DG`→`ο:d³`, `EF`→`ν:ef`, `EG`→`μ:e²`, `FG`→`ξ:f²`.
`BE` (`μ,ο`): `μ ⇒ 7b⁴ − 24b²e + 32e² = 0`, `ο/b ⇒ 21b⁴ − 160b²e + 320e² = 0` ⇒ `e = (11/28)b²` ⇒ `(123/49)b⁴ = 0`.
`CG` (`μ,π`): `μ ⇒ g = c²/8`, `π ⇒ 3c⁴ − 16c²g + 64g² = 2c⁴ = 0`.

**Pairs containing `A`, hand-checked:** `AB`→`μ:b⁴`, `AC`→`μ:c³` (`ξ^{AC} ≡ 0`, so `μ` must do it), `AE`→`μ:e²`, `AG`→**`π:g²`** (using `A⁴G = A⁸ = 0`).

**The all-even sub-family (where the leaf was really stuck).** On `B=D=F=0` the four odd integrals vanish identically, so only `μ, ξ, π` speak; their even restrictions are `A`-free (verified for `μ` and `ξ` including their `γ, ε, η` columns, see §5):

```
μ^ev = −(5/128)( C³ − 4E² − 8CG )       ξ^ev = (5/128) E ( 8G − 3C² )
π^ev = (5/256)( 3C⁴ − 16C²G − 32CE² + 64G² )
```

With `μ, ξ` alone `{C,E,G}` and `{A,C,E,G}` **survive** (`G = (3/8)C²`, `E² = −C³/2` is a genuine solution) — the real reason lanes 4–6 could not converge. Adding `π` gives `22C⁴ = 0`: dead. Likewise `{A,C,G}` → `2c⁴ = 0`, `{A,G}`/`{G}` → `g² = 0`, `{A,C,E}` → `ξ: c²e = 0`, `{A,E,G}` → `μ: e² = 0`.

**Prediction to be confirmed by CAS:** all 126 cones with `R ≠ {A}` are empty, the vast majority by a single monomial; the residual is the single cone `R = {A}`.

**If some other cone survives.** Two escapes, in order: (a) refine it by the σ-defect of §5 restricted to that cone (verified by hand on the pre-`π` survivors: `{C,G}`: `ν ⇒ d = 0`, `κ+ο ⇒ b = f = 0`; `{C,E,G}`: the odd-linear `4×3` matrix has rank 3 on `G=(3/8)C²`, `E²=−C³/2`); (b) if a cone with **all seven** letters survives (7 equations, 6 essential unknowns), use the auxiliary-combination trick of §6.

### The CAS job (`derive_810_scale_zero_quartic_cones.py`)

1. Read the seven Lean definitions verbatim (`degreeZeroXiPolynomial810`, `degreeZeroMuPolynomial810`, `degreeZeroOmicronPolynomial810`, `rho*GroupPolynomial810` for `Π`; `kappaResidual810`, `nuResidual810`, `piResidual810` with `alphaResidual810 → 0` and `βResidual…θResidual → β…θ`, `W₀ → θ + (…)`, `L → l`).
2. **Assert isobaricity** for weights `(11,12,13,14,15,16,17)` under `A,B,C₀,D₀,E₀,F₀,G₀,l,β,γ,δ,ε,ζ,η,θ ↦ 2,3,4,5,6,7,8,1,3,4,5,6,7,8,9`. Nothing proceeds until all seven pass.
3. Substitute the inverse of §2, expand, and assert the five hand-verified vanishings (`μ:A⁶`, `ξ:A⁷`, `π:A⁸`, `Π:A⁷B`, `Π:A⁶D`) plus `κ:A⁴B = −5/2048`. Emit the seven substituted definitions in Lean syntax.
4. Cross-check the seven `A=0` forms of §3 against the table above, coefficient by coefficient.
5. For each of the 127 nonempty `R ⊆ {A,…,G}`: form `{Φ_w^R : Φ_w^R ≠ 0}`, run the **saturated Gröbner test** `⟨Φ_w^R , T·Π_{ξ∈R} lc_ξ − 1⟩ = (1)` in `ℚ[lc_R, T]`. For empty cones, extract a certificate — the single monomial, or an explicit representation `(Π lc)^k = Σ h_i Φ_i^R` to transcribe as `linear_combination`.
6. For each cone and each integral, emit the "rest" polynomial and the list of ℕ inequalities that `compute_degree` + `omega` need, cross-multiplied (no division).

## 4. Prerequisite lane: put `κ`, `ν`, `π` in the packet

The current residual `normalized810ScaleZero_coneExhaustionResidual` (`Grok810ScaleZeroConeExhaustionScratch.lean:3069`, docstring `:3050`) exports only `ξ, μ, ο` constant and `Π` with `derivative = C (j/t)`. All three missing rows already exist and two are already *inside* the proof of the packet:

* `kappaResidual810_deriv_zero` (`Grok810ScaleZeroTenthDefectScratch.lean:1009`) — invoked as `hkappa0` at `Grok810ScaleZeroConeDefectFacesScratch.lean:4026`;
* `nuResidual810_deriv_zero` (`Fable810ScaleZeroTwelfthDefectScratch.lean`, mirrored at `Grok810ScaleZeroConeDefectFacesScratch.lean:4032` as `hnu0`), both consumed at `…:4285`;
* `piResidual810_deriv_zero` (`Sol810PiResidualScratch.lean:264`) and the source-facing `piResidual810_deriv_zero_of_monic_differentialJacobian` (`Sol810PiDifferentialBridgeScratch.lean:90`), used source-side at `Grok810PiSourceSplitScratch.lean:303–319` and `Grok810ScaleZeroClosureScratch.lean:601`.

The docstring of `normalized810ScaleZero_coneDefectFacesResidual` (`…ConeDefectFacesScratch.lean:4389`) says it outright: *"The unused first integrals `κ` and `ν` are available on that unique-`G₀` chamber."*

So this lane is a statement extension, not new mathematics: mirror `normalized810ScaleZero_defectPolynomials_eq_C` (`…ConeDefectFacesScratch.lean:3808`) to add

```lean
def degreeZeroKappaPolynomial810 (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) : k[X]
def degreeZeroNuPolynomial810     … : k[X]
def degreeZeroPiPolynomial810     … : k[X]      -- grouped like Π: piBaseGroup + 7 load groups
theorem normalized810ScaleZero_sevenIntegralPacket … :
    ∃ …, … ∧ (degreeZeroKappaPolynomial810 …).natDegree = 0
          ∧ (degreeZeroNuPolynomial810 …).natDegree = 0
          ∧ (degreeZeroPiPolynomial810 …).natDegree = 0 ∧ …
```

using the same `…_natDegree_eq_zero_of_eq_C` shims (`…ConeDefectFacesScratch.lean:3780–3796`) and the ground-constant extractions `normalized810ScaleZero_eleventhClearedDefect_exists_C` (`Grok810ScaleZeroEleventhDefectScratch.lean:2289`, degree bound `:2343`) and its tenth/twelfth analogues. File: **`Grok810ScaleZeroSevenIntegralPacketScratch.lean`**, importing `Grok810ScaleZeroConeExhaustionScratch`.

## 5. Stage B/C — inside `R = {A}`

Here every top form vanishes and each of `B…G` carries a **defect** `σ_ξ := w_ξρ − n_ξ > 0` (`= +∞` if `ξ = 0`); the `u`-degree of a load-free monomial is `wρ − Σ m_ξ σ_ξ`, and a load `π` costs a further `w_π ρ`.

**B0 (loads).** If the smallest active load defect `w_π ρ` undercuts the letter defects, the top of the relevant integral is a single monomial `coeff·π·A^i` ⇒ that load vanishes. Iterate over `l(1), β(3), γ(4), δ(5), ε(6), ζ(7), η(8), θ(9)` exactly as (6,10)'s B0.

**B1 (odd letters die first — the uniform step).** Every monomial of an odd integral has at least one of `B, D, F`; monomials with three of them have defect `≥ 3τ`. Hence with `τ := min{σ_B, σ_D, σ_F}` over the nonzero odd letters and `T := argmin`,

```
in_τ(Φ) = Σ_{Y ∈ T} lc_Y · (∂Φ₀/∂Y)|_{B=D=F=0, other letters ↦ 0}
```

*independently of what the even letters do.* On `R = {A}` those partials are pure powers of `A`, so with `u := a⁴b, v := a³d, w := a²f` the four equations become a **constant `4×3` matrix**

| | `B` | `D` | `F` |
|---|---|---|---|
| `κ` (11) | `A⁴B` = **−5/2048** | `A³D` | `A²F` |
| `ν` (13) | `A⁵B` | `A⁴D` | `A³F` |
| `ο` (15) | `A⁶B` | `A⁵D` | `A⁴F` |
| `Π` (17) | `A⁷B` = **0** | `A⁶D` = **0** | `A⁵F` |

**If this matrix has rank 3, all of `B, D, F` vanish identically** — one lemma, no chamber enumeration. (Two bold entries verified by hand; the remaining nine entries are a one-line CAS extraction.)

**B2 (the even core).** With `B = D = F = 0` the four odd integrals are identically zero and the leaf collapses to the depressed **quartic** `φ(z) = z⁴ + Cz² + Ez + G`, `f = φ(q)`. `μ` and `ξ` — including *all* their load columns — are then `A`-free:

```
μ|even = −(5/128)(C³ − 4E² − 8CG) + (3/32)γ(8G − C²) + (1/2)εE + (1/4)ηC
ξ|even =  (5/128)E(8G − 3C²)      − (3/16)γCE + (1/8)ε(4G − C²) + (1/4)ηE
π|even =  (5/256)(3C⁴ − 16C²G − 32CE² + 64G²) + γ(…) + ε(…) + (1/4)η(8G − C²)
```

(the last `η`-column computed from `piEtaGroup810`, `Sol810PiResidualScratch.lean:66`; its `A⁴`, `A²C`, `AE` coefficients all cancel). So on the even core the problem is a **three-letter** argmax over `{C,E,G}` with three integrals, and all seven of its cones die at level 0:

`{C}`→`μ:c³`, `{E}`→`μ:e²`, `{G}`→`π:g²`, `{C,E}`→`ξ:c²e`, `{E,G}`→`μ:e²`, `{C,G}`→`μ,π: 2c⁴`, `{C,E,G}`→`μ,ξ,π: 22c⁴`.

Hence `C, E, G` are all **constants**.

**B3 (endgame).** With `B=D=F=0` and `C, E, G` constant, every integral is a univariate polynomial in `A` with load coefficients. `Π`'s `θ`-column is (from `rhoThetaGroupPolynomial810`, `…ConeEliminationScratch.lean:264`)

```
(5/4096)A⁴ + (3/128)A²C − (1/16)C² + (1/8)AE + G ,
```

so `natDegree Π = 1` with `derivative Π = C(j/t) ≠ 0` forces `A` linear or constant, and then a bounded linear-algebra contradiction in the loads. The all-constant sub-case is already closed: `degreeZeroPrimitivePolynomial810_false_of_constant_core` (`…ConeEliminationScratch.lean:1564`), and the `G₀`-degree cases by `uniqueNonconstantG0_impossible_of_l_ne` (`…ConeEliminationScratch.lean:2030`), `uniqueHighG0DegGtOne_l0_impossible` (`…ConeExhaustionScratch.lean:3012`) and `uniqueHighG0DegOne_existsPrimitive_false` (`Grok810ScaleZeroClosureScratch.lean:601`).

## 6. The `N₁` analogue (needed only if a large cone survives)

(6,10) needed `N₁ := μ + (A/6)κ` because on the balanced cell the *odd* forms were proportional. Here the proportionality to look for is the **parity-split syzygy**: on a cone `R` where the seven initial forms are dependent, take the combination `N := Σ h_i(A)·Φ_i` whose initial form vanishes, note `natDegree N ≤ max_i (deg h_i)` (from `natDegree Φ_i = 0`, `natDegree Π = 1`), and read off the next-order equation. Candidates, in decreasing priority:

* `N₁ := μ + c·A·κ` (weight 12, `natDegree ≤ n_A`) — the direct transcription of the (6,10) trick; `κ`'s `A⁴B` is the only nonzero one-letter face, so `N₁` is the natural separator of the load columns from the letter columns.
* `N₂ := π + c′·A·ο + c″·A²·μ` (weight 16) on the even core, which carries the `γ`-column and therefore makes B0 uniform.

The auxiliary integral that separates them is **`π` itself**: the only even integral whose restriction to `{G}` is nonzero (`(5/4)G²`), so it breaks every tie in which `G` participates.

## 7. Lean lemma sequence

Namespace `Max11DegreeRoutes`. Three files, each importing the previous; the first imports `Grok810ScaleZeroConeExhaustionScratch` (the deepest tracked node of the chain `FinalRow → ConeElimination → ConeDefectFaces → ConeRatioTies → Closure → MixedCones → ConeExhaustion`).

### 7.0 `Grok810ScaleZeroSevenIntegralPacketScratch.lean` — §4 above.

### 7.1 `Grok810ScaleZeroQuarticConesScratch.lean` (Stage A)

```lean
def quarticC810 (A C0 : k[X]) : k[X] := C0 - (3/8 : k) • A ^ 2
def quarticD810 (A B D0 : k[X]) : k[X] := D0 - (1/2 : k) • (A * B)
def quarticE810 (A C0 E0 : k[X]) : k[X] := E0 - (1/2 : k) • (A * C0) + (1/8 : k) • A ^ 3
def quarticF810 (A B D0 F0 : k[X]) : k[X] := F0 - (1/4 : k) • (A * D0) + (1/16 : k) • (A ^ 2 * B)
def quarticG810 (A C0 E0 G0 : k[X]) : k[X] :=
  G0 - (1/4 : k) • (A * E0) + (1/16 : k) • (A ^ 2 * C0) - (3/256 : k) • A ^ 4

def degreeZeroKappaQuartic810   (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X]
def degreeZeroMuQuartic810      … ; degreeZeroNuQuartic810 … ; degreeZeroXiQuartic810 …
def degreeZeroOmicronQuartic810 … ; degreeZeroPiQuartic810 … ; degreeZeroPrimitiveQuartic810 …

theorem degreeZeroMuPolynomial810_eq_quartic
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B (C + (3/8 : k) • A ^ 2) (D + (1/2 : k) • (A * B))
        (E + (1/2 : k) • (A * C) + (1/16 : k) • A ^ 3)
        (F + (1/4 : k) • (A * D) + (1/16 : k) • (A ^ 2 * B))
        (G + (1/4 : k) • (A * E) + (1/16 : k) • (A ^ 2 * C) + (1/256 : k) • A ^ 4)
      = degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G
```

one per integral, proof `simp only [defs]; ring`. Split `Π` and `π` into their eight group identities to stay inside the heartbeat budget, mirroring `rhoBaseGroupPolynomial810_eq_A8_add_rest` (`…ConeEliminationScratch.lean:822`, `set_option maxHeartbeats 16000000`) and `degreeZeroPrimitivePolynomial810_eq_A8_add_rest` (`:831`). Then a wrapper turning the packet's `(A,B,C₀,…,G₀)` into `(A,B,quarticC810 …, …)` by `sub_add_cancel`-style rewriting.

**Cone predicates** — 127 defs in cross-multiplied ℕ form, e.g.

```lean
def QuarticRatioConeCEG810 (A B C D E F G : k[X]) : Prop :=
  0 < C.natDegree ∧ 3 * C.natDegree = 2 * E.natDegree ∧ C.natDegree = 2 * G.natDegree ∧
    2 * C.natDegree < 4 * A.natDegree ∧ 3 * C.natDegree < 4 * B.natDegree ∧ …
```

(state every comparison cross-multiplied; never divide, so `omega` can finish).

**Per-integral split + rest bounds** — the existing proven shape:

```lean
theorem degreeZeroMuQuartic810_eq_CEG_add_rest … :
    degreeZeroMuQuartic810 … = muCEGFace810 C E G + degreeZeroMuQuarticNoCEG810 …
theorem degreeZeroMuQuarticNoCEG810_natDegree_lt … (hcone : QuarticRatioConeCEG810 …) :
    (degreeZeroMuQuarticNoCEG810 …).natDegree < 3 * C.natDegree
```

proved by `compute_degree` then `omega`, literally the shape of `degreeZeroMuNoA6_natDegree_lt_of_mixedB` (`…ConeExhaustionScratch.lean:1403`) and `…_of_mixedC0` (`:1441`).

**Cone kills** — 126 theorems, most `exact absurd … (mul_ne_zero …)` on a single monomial, the rest a transcribed `linear_combination` (Gröbner certificate), each wrapped in the `by_cases hI : innerForm = 0` pattern of `mu_xi_AC02_impossible` (`…ConeExhaustionScratch.lean:2428`) and `mu_xi_AE06_impossible` (`:2560`).

**Export:** `normalized810ScaleZero_quarticADominantResidual` — the packet plus `¬ QuarticRatioCone…810` for all 126, i.e. the single surviving cone `R = {A}`.

### 7.2 `Grok810ScaleZeroQuarticADominantScratch.lean` (Stage B)

`QuarticSigmaCone…810` predicates (linear identities in `n_A,…,n_G`, cross-multiplied); load-killing lemmas `quarticADominant_l_eq_zero`, `…_beta_eq_zero`, …, `…_theta_eq_zero`; the odd-letter kill

```lean
theorem quarticADominant_oddLetters_eq_zero … : B = 0 ∧ D = 0 ∧ F = 0
```

from the rank-3 `4×3` matrix; then the even-core cone kills (7 lemmas) giving `C.natDegree = E.natDegree = G.natDegree = 0`, then `quarticEvenCore_impossible` from `derivative Π = C (j/t)` reusing `degreeZeroPrimitivePolynomial810_false_of_constant_core` (`…ConeEliminationScratch.lean:1564`).

### 7.3 Assembly

```lean
theorem normalized810ScaleZero_impossible {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) : False
theorem planeKeller810ScaleZeroExclusion_closed : PlaneKeller810ScaleZeroExclusion (K := K) :=
  planeKeller810ScaleZeroExclusion_of_impossible normalized810ScaleZero_impossible
```

Exhaustiveness: nested `by_cases` on the 21 pairwise ratio comparisons, closing leftovers with `omega` — the tail of the existing `normalized810ScaleZero_coneExhaustionResidual` proof (`…ConeExhaustionScratch.lean:3110–3210`) is the template.

## 8. CAS jobs the lane must run **before** writing Lean

1. `derive_810_scale_zero_quartic_coordinates.py` — §3 steps 1–4: isobaricity assertion for all seven weights (the transcription checksum), the substitution, the five pure-`A` vanishings, the seven `A=0` forms, and Lean-syntax emission of the seven quartic definitions.
2. `derive_810_scale_zero_quartic_cones.py` — §3 steps 5–6: the 127 saturated Gröbner tests, certificates, rest polynomials, and ℕ-inequality lists.
3. `derive_810_scale_zero_quartic_adominant.py` — the nine remaining entries of the odd `4×3` matrix and its rank; the σ-grading (minimal σ-degrees of all seven forms in `R = {A}`); the **complete** load enumeration (`2⁸` load subsets × `2⁶` letter-vanishing subsets × exact σ-grid) verifying that no chamber other than the even core survives.
4. `derive_810_scale_zero_quartic_evencore.py` — the three even forms with all load columns on `B=D=F=0`, their `A`-freeness, the seven even-cone certificates, and the `A`-linear endgame of B3.
5. `derive_810_scale_zero_quartic_auxiliary.py` — only if (2) leaves a survivor: the `N₁`/`N₂` combinations of §6 and their next-order forms.

## 9. Reuse map (file:line)

* route: `PlaneKeller810ScaleZeroExclusion`, `Grok810RouteAdapterScratch.lean:27`; `planeKeller810ScaleZeroExclusion_of_impossible`, `Grok810ScaleZeroConeEliminationScratch.lean:2266`
* entry residual + consumer: `normalized810ScaleZero_coneExhaustionResidual` `Grok810ScaleZeroConeExhaustionScratch.lean:3069`; `normalized810ScaleZero_impossible_of_exhaustionResidual` `:3213`
* integral definitions: `degreeZeroXiPolynomial810` `Grok810ScaleZeroConeDefectFacesScratch.lean:180`; `degreeZeroMuPolynomial810` `:278`; `degreeZeroOmicronPolynomial810` `:342`; `degreeZeroPrimitivePolynomial810` `Grok810ScaleZeroConeEliminationScratch.lean:744` with groups `:168, :193, :212, :230, :243, :255, :264, :274`
* unused rows: `kappaResidual810` `Grok810ScaleZeroTenthDefectScratch.lean:91`, `_deriv_zero` `:1009`; `nuResidual810` `Fable810ScaleZeroTwelfthDefectScratch.lean:86`; `piResidual810` `Sol810PiResidualScratch.lean:113`, `piBaseGroup810` `:74`, `_deriv_zero` `:264`, source bridge `Sol810PiDifferentialBridgeScratch.lean:90`, source use `Grok810PiSourceSplitScratch.lean:303`
* packet to extend: `normalized810ScaleZero_defectPolynomials_eq_C` `…ConeDefectFacesScratch.lean:3808` (κ/ν already present at `:4026`, `:4032`, consumed `:4285`); `…_defectFaces_closed` `:4317`; `…_coneDefectFacesResidual` `:4389`
* natDegree helpers: `natDegree_eq_one_of_derivative_eq_nonzero_C810` `…ConeEliminationScratch.lean:68`; `natDegree_add_lt810` `:82`; `natDegree_add_le810` `:87`; `natDegree_smul_le810` `:92`; `natDegree_smul_lt810` `:99`; `natDegree_smul_le_of_le810` `:103`; `natDegree_eq_zero_of_le_zero` `:107`; `natDegree_add8_lt810` `:111`; `natDegree_add8_le810` `:128`
* split-lemma + `module` pattern and heartbeat settings: `rhoBaseGroupPolynomial810_eq_A8_add_rest` `…ConeEliminationScratch.lean:822`; `degreeZeroPrimitivePolynomial810_eq_A8_add_rest` `:831`; `…_eq_C04_add_rest` `:910`; `…_eq_G02_add_rest` `:933`
* rest-bound `compute_degree`+`omega` pattern: `…ConeExhaustionScratch.lean:1403–1750`; zero-power simp shims `…ConeExhaustionScratch.lean:155–175`
* two-integral `by_cases` kill pattern: `mu_xi_AC02_impossible` `…ConeExhaustionScratch.lean:2428`; `mu_xi_ABC0_impossible` `:2553`; `mu_xi_AE06_impossible` `:2560`
* final `by_cases` + `omega` assembly: `…ConeExhaustionScratch.lean:3110–3210`
* degenerate chambers already closed: `degreeZeroPrimitivePolynomial810_false_of_constant_core` `…ConeEliminationScratch.lean:1564`; `uniqueNonconstantG0_impossible_of_l_ne` `:2030`; `uniqueHighG0DegGtOne_l0_impossible` `…ConeExhaustionScratch.lean:3012`; `uniqueHighG0DegOne_existsPrimitive_false` `Grok810ScaleZeroClosureScratch.lean:601`
* precedent: `Grok610ScaleZeroCubicCoordinateTowerPlanScratch.md` (the whole method); `Grok68TerminalZeroMeetingCellPlanScratch.md` §2 (the (6,8) cubic coordinates)

## 10. Risks (honest)

1. **Transcription.** All coefficients above were read off the Lean text by hand. Mitigation: the isobaricity assertion in CAS job 1 (passed by hand on every group of all seven objects), plus the five independent pure-`A` cancellations of §2, plus the `μ`/`ξ` face table.
2. **Stage A completeness.** 6 singles + 15 pairs without `A` + 4 pairs with `A` + the 7 all-even cones verified by hand. The remaining ~95 cones are the CAS job. The genuinely tight one is the full cone `R = {A,…,G}`: 7 equations in 6 essential unknowns. If it survives, §6 is the tool.
3. **The `A`-freeness of the even restrictions** (`μ|even`, `ξ|even`, `π|even`) is verified for `μ` and `ξ` including their three load columns and for `π`'s `η`-column and `A⁸`/`A⁴G` faces; the `π` `γ`- and `ε`-columns are a CAS check. If it fails, `{A,C,E,G}` needs the odd-linear stage of §5 B1.
4. **Rank of the odd `4×3` matrix** in `R = {A}` — the one genuinely uncomputed number set. If it is rank 2, use `N₁ = μ + cAκ` of §6 to expose the next order.
5. **`ring`/`module` cost of the transport.** `Π` after substitution has ~90 monomials with `A`-powers to 8, and `π` similar. Mitigate with the eight-group split and `maxHeartbeats 32000000`, as at `…ConeEliminationScratch.lean:822`. Also the Tier-1 performance rules (linters off; cleared identities).
6. **Cone exhaustiveness in ℕ.** 127 cones need 21 cross-multiplied ratio comparisons; state them all without division and let `omega` finish.
7. Nothing here uses a total-degree theorem, a twice-prime theorem, a finite-root shortcut, or a new axiom.

## 11. Fallbacks

* **F1 (staging).** Split into four lanes: L0 = §4 (packet extension, cheap — the facts are already inside the existing proof); L1 = §7.1 (coordinates + 126 cone kills) exporting `normalized810ScaleZero_quarticADominantResidual`; L2 = §7.2 B0/B1 (loads + odd letters vanish) exporting the even-core residual; L3 = B2/B3 + assembly. **L0 + L1 alone already reduce the leaf from six open lanes to one cone.**
* **F2 (if a large cone survives Stage A).** Promote `N₁ = μ + cAκ` and `N₂ = π + c′Aο + c″A²μ` to first-class objects at the start of Stage A.
* **F3 (if the even core resists in Lean).** On `B = D = F = 0` the octic is `φ(y² + A/4)` for the depressed quartic `φ(z) = z⁴ + Cz² + Ez + G`, and `μ|even, ξ|even, π|even` are polynomials in `C, E, G` (no `A`). Eliminate `G` from `ξ`, then `E` from `μ`, exhibit `C, E, G ∈ k[c]` and close with `Polynomial.derivative_comp` against `derivative Π = C (j/t)` — the (6,8) meeting-cell finish.
* **Bonus.** The *count* rule ("as many integrals of weights `m+n−1−(ℓ−1) … m+n−1` as there are letters `ℓ`") predicts exactly which rows a stalled leaf is missing.
