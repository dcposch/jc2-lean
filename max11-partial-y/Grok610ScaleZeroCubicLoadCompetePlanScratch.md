# Plan: closing `normalized610ScaleZero_cubicResidual5` (the last (6,10) scale-zero chamber) — Opus, 2026-09-04

## 0. Summary of the decisive finding

The residual left by `normalized610ScaleZero_cubicResidual5` (`Grok610ScaleZeroCubicLoadCompeteScratch.lean:704`) is

> `CubicRatioConeA610 A B C D E` ∧ `cubicLoadCompetes610 A B C D E` ∧ `l = 0`, with the three implications `cubicKappaBetaTop610 → β = 0`, `cubicKappaDeltaTop610 → δ = 0`, `cubicKappaZetaTop610 → ζ = 0`.

Write `a,b,c,d,e := A.natDegree,…,E.natDegree`, `ρ := a/2`, and
`12·τ_B = 9a−6b`, `12·τ_C = 12a−6c`, `12·τ_D = 10a−4d`, `12·τ_E = 12a−4e`, `T := 12·Θ = min τ` (over the **nonzero** letters). Then

* `cubicLoadCompetes610` (`Grok610ScaleZeroCubicADominantScratch.lean:258`) is exactly `T ≥ a` (each conjunct `4a ≥ 3b`, `11a ≥ 6c`, `9a ≥ 4d`, `11a ≥ 4e` is `12τ_X ≥ a`);
* the κ σ-6 letter face sits at degree `(11a − T)/2`, and the odd pure-`A` columns of κ sit at `5a, 4a, 3a, 2a, a` for `l, β, δ, ζ, θ`;
* `cubicKappaBetaTop610`/`DeltaTop`/`ZetaTop` are (implied by) `T > 3a`, `T > 5a`, `T > 7a`.

**The three lanes stalled because they tried to close the region `a ≤ T ≤ 3a` in κ.** In κ the β-column ties the letter face exactly at `T = 3a`, so the κ route unavoidably produces "mixed" chambers, and the θ-column (degree `a`) is *never* the strict top of κ (it is always tied or beaten by `A B³`, degree `a+3b ≥ a`). So κ can in principle never kill θ.

**The fix is `N₁ = μ + (A/6)κ`.** Its σ-6 part vanishes identically, so its letter face is σ-7, at degree `(78a − 7T)/12`, while its odd columns are
`77/248832·l·A⁶`, `7/6912·β·A⁵`, `35/10368·δ·A⁴`, `5/432·ζ·A³`, `1/24·θ·A²`
(`Grok610ScaleZeroCubicADominantScratch.lean:274`, `Grok610ScaleZeroCubicBalancedScratch.lean:614–623`), and `degreeZeroN1Cubic610_natDegree_le` (`…ADominantScratch.lean:342`) bounds `natDegree N₁ ≤ a`. Hence the π-column strictly tops N₁ iff

| load | κ-route condition | **N₁ condition** |
|---|---|---|
| β | `T > 3a` | `7T > 18a` (`18/7 ≈ 2.571 a`) |
| δ | `T > 5a` | `7T > 30a` (`≈ 4.286 a`) |
| ζ | `T > 7a` | `T > 6a` |
| θ | *impossible* | `7T > 54a` (`≈ 7.714 a`) |

Meanwhile the σ-face of **λ and ο**, which have **no pure-`A` load column at all** (CAS `out_610_scale_zero_cubic_adominant.json`, `load_columns: {"lambda": {}, "omicron": {}}`), strictly tops its own integral as long as `T < 9a/2` (β alive), `T < 15a/2` (β=0), `T < 21a/2` (β=δ=0), `T < 27a/2` (β=δ=ζ=0), `T < 12a` (all odd dead).

Because `18/7 < 9/2`, `30/7 < 15/2`, `6 < 21/2`, `54/7 < 27/2`, **the N₁ kill regions and the face-top regions overlap strictly**. Therefore:

> **There are no tie ("mixed") chambers at all** once the odd loads are killed through `N₁` instead of κ. Every chamber is a *strict* face chamber, and the whole residual reduces to the 15 σ-argmin cones already solved by CAS, re-stated on the load-compete side.

---

## 1. Enumeration of the letter-topped / mixed cases (as they actually stand)

### 1.1 Which odd columns survive `Grok610ScaleZeroCubicLoadCompeteScratch`

`l` is dead (`cubicADominant_l_eq_zero`, `…ADominantScratch.lean:3255`, via `n1CubicLFace610` at `6a` and `degreeZeroN1CubicNoL610_natDegree_lt_of_loadCompete` :3239 — valid on *all* of `cubicLoadCompetes610`). Surviving columns in κ: `β A⁴` (4a), `δ A³` (3a), `ζ A²` (2a), `θ A` (a).

### 1.2 `β A⁴`: `¬ cubicKappaBetaTop610` (`…LoadCompeteScratch.lean:171`)

Given `cubicLoadCompetes610`, the negation is the disjunction (cross-multiplied ℕ, no division; verified against `degreeZeroKappaCubic610`, `Grok610ScaleZeroCubicConesScratch.lean:91`):

| # | monomial of κ | ties/beats `β A⁴` iff | implies |
|---|---|---|---|
| β1 | `(5/243)•(A*B^3)` | `4a ≤ a + 3b` (i.e. `a ≤ b`) | `T ≤ 3a` |
| β2 | `−(5/27)•(B*C^2)` | `4a ≤ b + 2c` | `T ≤ 3a` |
| β3 | `−(5/27)•(B^2*D)` | `4a ≤ 2b + d` | `T ≤ 3a` |
| β4 | `(10/9)•(D*E)` | `4a ≤ d + e` | `T ≤ 3a` |
| β5 | `(4/9·α)•(C*D)` | `4a ≤ c + d` | `5T ≤ 6a` |

No other κ monomial can reach `4a` — exactly what `degreeZeroKappaCubicNoBetaA4_l0610_natDegree_lt_of_betaTop` (`…LoadCompeteScratch.lean:255`) certifies.

### 1.3 `δ A³`, `ζ A²`: `¬ cubicKappaDeltaTop610` (:179) / `¬ cubicKappaZetaTop610` (:188)

Same list with `4a` replaced by `3a` (resp. `2a`), plus the extra competitor `α B E` (`3a ≤ b+e`, resp. `2a ≤ b+e`). Implications: `¬DeltaTop ⇒ T ≤ 5a`, `¬ZetaTop ⇒ T ≤ 7a`.

### 1.4 `θ A`

`A B³` has degree `a + 3b ≥ a` always, so `θ A` is *never* the strict top of κ. **The θ column must be taken in `N₁` (degree `2a`).**

### 1.5 Verification against the CAS

`scripts/derive_610_scale_zero_cubic_wall_mixed.py` enumerates, for every `S ⊆ {B,C,D,E}`, the `letter_only` system and the four `mixed_{beta,delta,zeta,theta}` systems. `scripts/out_610_scale_zero_cubic_wall_mixed.json` reports `closed = 79`, `survivors = 1`, the survivor being the vacuous empty-`S` record. **With the N₁ ladder every chamber is a strict letter-face chamber, so only the 15 `letter_only` certificates are required — and all three non-monomial ones already exist in Lean (§2).**

---

## 2. Face equations and certificates, per σ-argmin cone `S`

| `S` | `T_S` | carrier | face | face degree | top-coefficient identity | certificate |
|---|---|---|---|---|---|---|
| `B` | `9a−6b` | κ | `(5/243)•(A*B^3)` | `a+3b` | `a·b³ = 0` | `mul_ne_zero` |
| `C` | `12a−6c` | λ | `−(5/81)•C^3` | `3c` | `c³ = 0` | monomial |
| `D` | `10a−4d` | λ | `−(5/27)•(A*D^2)` | `a+2d` | `a·d² = 0` | monomial |
| `E` | `12a−4e` | λ | `(5/9)•E^2` | `2e` | `e² = 0` | monomial |
| `BC` | tie | κ **and** λ | `κ: (5/243)AB³−(5/27)BC²`; `λ: (5/81)AB²C−(5/81)C³` | `a+3b`; `a+2b+c` | both `= 0` | **`cubicSigmaInner_BC_identity`, `…ADominantScratch.lean:876`** (`c⁵`) |
| `BD` | tie | λ | `−(5/27)•(A*D^2)` | `a+2d` | `a·d²` | monomial |
| `BE` | tie | λ | `(5/9)•E^2` | `2e` | `e²` | monomial |
| `CD` | tie | **N₁** | `n1CubicSigmaFaceCD610 = −(5/27)•(C^2*D)` | `2c+d` | `c²·d = 0` | monomial; see §5 wall |
| `CE` | tie | ο | `−(5/27)•(C^2*E)` | `2c+e` | `c²·e` | monomial |
| `DE` | tie | κ | `(10/9)•(D*E)` | `d+e` | `d·e` | monomial |
| `BCD` | tie | ο | `(10/81)•(A*B*C*D)` | `a+b+c+d` | `a·b·c·d` | monomial |
| `BCE` | tie | κ, λ, ο | inners `5ab³−45bc²`, `5ab²c−5c³+45e²`, `5ab²e−15c²e` | | all `= 0` | **`cubicSigmaInner_BCE_identity`, :1740** (`c⁷`) |
| `BDE` | tie | ο | `(5/81)•(A*B^2*E)` | `a+2b+e` | `a·b²·e` | monomial |
| `CDE` | tie | ο | `−(5/27)•(C^2*E)` | `2c+e` | `c²·e` | monomial |
| `BCDE` | tie | κ, λ, ο, **N₁** | `G1..G4` | | all four `= 0` | **`cubicSigmaInner_BCDE_identity`, :2870** (`e⁵`) |

12 of 15 cones close on one integral (single monomial); nine of those use λ or ο, which carry no pure-`A` load column, so their rest bounds need no column splitting. `BC` needs κ+λ; `BCE` κ+λ+ο; `BCDE` κ+λ+ο+N₁; `CD` needs N₁ only (N₂ enters only on the β-wall, §5). Π is needed once, for the degenerate corner (§3.6). All three genuine certificates and the `_coeff_top` lemmas (`kappaCubicSigmaFaceBC610_coeff_top` :956, `lambdaCubicSigmaFaceBC610_coeff_top` :1057, the four `…FaceBCDE610_coeff_top` :2879/:2911/:2949/:2981, `n1CubicSigmaFaceCD610_coeff_top` `…BalancedScratch.lean:141`) are reusable; where a cone hypothesis is threaded, re-prove against the new load-compete cone with the same body.

---

## 3. The Lean rest-bound recipe

New files importing `Grok610ScaleZeroCubicLoadCompeteScratch`.

### 3.1 Correctly tuned N₁ column predicates (file A)

> **Do not reuse `cubicLoadCompetesBeta610/Delta/Zeta/Theta610` (`…ADominantScratch.lean:3289, 3297, 3305, 3313`).** They are sound but far too small (`T ≥ 19a/3` instead of `7T > 18a`). Replace them:

```lean
/-- `7 Θ > 3 ρ`: the `β A⁵` column of `N₁` strictly tops `N₁`. -/
def cubicN1BetaTop610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧
    14 * B.natDegree < 15 * A.natDegree ∧ 7 * C.natDegree < 11 * A.natDegree ∧
    7 * D.natDegree < 13 * A.natDegree ∧ 14 * E.natDegree < 33 * A.natDegree

/-- `7 Θ > 5 ρ`. -/
def cubicN1DeltaTop610 … := cubicLoadCompetes610 … ∧
    14 * B.natDegree < 11 * A.natDegree ∧ 7 * C.natDegree < 9 * A.natDegree ∧
    7 * D.natDegree < 10 * A.natDegree ∧ 14 * E.natDegree < 27 * A.natDegree

/-- `Θ > ρ`. -/
def cubicN1ZetaTop610 … := cubicLoadCompetes610 … ∧
    2 * B.natDegree < A.natDegree ∧ C.natDegree < A.natDegree ∧
    D.natDegree < A.natDegree ∧ 2 * E.natDegree < 3 * A.natDegree

/-- `7 Θ > 9 ρ`. -/
def cubicN1ThetaTop610 … := cubicLoadCompetes610 … ∧
    14 * B.natDegree < 3 * A.natDegree ∧ 7 * C.natDegree < 5 * A.natDegree ∧
    7 * D.natDegree < 4 * A.natDegree ∧ 14 * E.natDegree < 15 * A.natDegree
```

Re-prove, with the existing rest defs untouched, the four bounds `degreeZeroN1CubicNoLNoBetaA5610_natDegree_lt_of_N1BetaTop` (`< 5a`, copy the proof at `…BalancedScratch.lean:677` verbatim: rcases the cone, `have hB1 …`, `simp only [def]; compute_degree; omega`), and the analogues for `degreeZeroN1CubicNoLNoBetaNoDeltaA4610` (:725, `< 4a`), `degreeZeroN1CubicNoOddPureANoZetaA3610` (:814, `< 3a`), `degreeZeroN1CubicNoOddPureANoThetaA2610` (:898, `< 2a`) — hand-checked: all monomials strictly below. Then restate `cubicADominant_beta_eq_zero` (:693), `_delta_` (:781), `_zeta_` (:864), `_theta_` (:944) against the new predicates; proof bodies unchanged.

### 3.2 Load-compete σ-argmin cones (file A)

15 defs from `CubicSigmaConeB610 … CubicSigmaConeBCDE610` (`…ADominantScratch.lean:46–255`) by three mechanical edits: (1) replace the first five conjuncts by `cubicLoadCompetes610 A B C D E`; (2) **delete the final strict conjunct** (its negation *is* load-compete); (3) replace `0 < X.natDegree` by `X ≠ 0` for `X ∈ S`, and wrap each "`Y ∉ S`" comparison as `Y = 0 ∨ (strict comparison)`. Example:

```lean
def CubicLoadSigmaConeCD610 (A B C D E : k[X]) : Prop :=
  cubicLoadCompetes610 A B C D E ∧ C ≠ 0 ∧ D ≠ 0 ∧
    5 * A.natDegree + 3 * C.natDegree = 6 * A.natDegree + 2 * D.natDegree ∧
    (B = 0 ∨ A.natDegree + 2 * B.natDegree < 2 * C.natDegree) ∧
    (E = 0 ∨ 2 * E.natDegree < 3 * C.natDegree)
```

Exhaust `cubicLoadSigmaSupportCone610_of`, modelled on `cubicSigmaSupportCone610_of` (`Grok610ScaleZeroCubicWallScratch.lean:866`, `CubicSigmaSupportCone610` :846): nested `by_cases hXz : X = 0` for the four letters, then `by_cases` on the six pairwise `12τ` comparisons; `Y = 0` leaves take `Or.inl`; `allZero` discharged by `cubicADominant_allLettersZero_impossible` (`…ADominantScratch.lean:3043`).

### 3.3 Per-cone split defs (files B–C)

Reuse the existing face/rest pairs (`kappaCubicSigmaFaceB610`/`degreeZeroKappaCubicNoSigmaB610` :453/:457, `lambdaCubicSigmaFaceC610` :556, `…FaceD610` :659, `…FaceE610` :767, `kappa/lambdaCubicSigmaFaceBC610` :884/:981, `…FaceBD610` :1176, `…FaceBE610` :1279, `omicronCubicSigmaFaceCE610` :1382, `kappaCubicSigmaFaceDE610` :1500, `omicronCubicSigmaFaceBCD610` :1603, `…FaceBCE610` :1749/:1846/:1954, `…FaceBDE610` :2184, `kappaCubicSigmaFaceCDE610` :2306, `lambdaCubicSigmaFaceCD610` :2415, the four `…FaceBCDE610`, `n1CubicSigmaFaceCD610` (`…BalancedScratch.lean` ~:141), `n1CubicSigma7Face610` :373). **The `_eq_face_add_rest` split theorems (`…_eq_sigmaB_add_rest` :492 etc.) are cone-free `module` identities and reusable verbatim.** Only the `_natDegree_lt` lemmas are new.

### 3.4 The rest-bound lemma shape (the missing row)

One lemma per `(S, carrier)`, covering all five bands by disjunctive hypotheses. Model `degreeZeroKappaCubicNoSigmaB610_natDegree_lt` (`…ADominantScratch.lean:503`) and `degreeZeroKappaCubicNoBetaA4_l0610_natDegree_lt_of_betaTop` (`…LoadCompeteScratch.lean:255`):

```lean
set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoSigmaB610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeB610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) ≤ 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) ≤ 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨      9 * A.natDegree  ≤  6 * A.natDegree +  6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) ≤ 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroKappaCubicNoSigmaB610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree
      < A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCcmp, hDcmp, hEcmp⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  …                                        -- one `Nat.succ_le_of_lt` per strict conjunct
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
    rcases hCcmp with rfl | hCcmp <;> rcases hDcmp with rfl | hDcmp <;>
    rcases hEcmp with rfl | hEcmp <;>
      (simp only [degreeZeroKappaCubicNoSigmaB610, zero_mul, mul_zero, zero_smul,
                  add_zero, zero_add, zero_pow, Nat.succ_ne_zero];
       compute_degree; omega)
```

The disjuncts are the band inequalities `7 T_S ≤ 18a`, `7 T_S ≤ 30a`, `T_S ≤ 6a`, `7 T_S ≤ 54a` with `T_S` expanded and subtraction cleared. Hand-verified bands (F := κ face degree `(11a − T)/2`): band 0 `14F ≥ 59a > 56a`; band 1 `14F ≥ 47a > 42a`; band 2 `2F ≥ 5a > 4a`; band 3 `14F ≥ 23a > 14a`; band 4 needs only `T < 12a`. All strict: **no tie chamber occurs.** Prefer pre-substituted rest defs per band (as `…LoadCompeteScratch.lean:71/110/143` do) over the `<;>` chain if heartbeats blow up.

### 3.5 Top-coefficient extraction and kill

Copy `cubicSigmaCone_B_impossible` (`…ADominantScratch.lean:525`): `hlead` for the face degree, the new rest bound, `rw [degreeZero…_eq_sigmaS_add_rest, natDegree_add_eq_left_of_natDegree_lt …, hlead] at hdeg; omega`. Multi-monomial faces: read coefficients with the `_coeff_top` lemmas and apply the identity exactly as `cubicBalancedCell_impossible` (`…BalancedScratch.lean:512–560`). For the N₁ carriers (`CD`, `BCDE`) the kill is a `natDegree` contradiction against `degreeZeroN1Cubic610_natDegree_le` (`≤ a`): `2c + d > a` by `omega`. Model `cubicSigmaCone_CD_impossible` (`…BalancedScratch.lean:167`).

### 3.6 The two degenerate corners

* **`faceDeg = 0`.** Only `S = {C}`, `{E}`, `{C,E}` can have a zero-degree face; `omega` gives `T = 12a`, forcing `B = 0` and `D = 0`, and band 4.
* **`B = 0 ∧ D = 0` with `l = β = δ = ζ = θ = 0` ⇒ `Π ≡ 0`** (every base-group and α/ε/η monomial of `degreeZeroPrimitiveCubicFlat610`, `Grok610ScaleZeroCubicConesScratch.lean:471`, contains `B` or `D`):

```lean
theorem cubicLoadCompete_BD_zero_impossible {j t : k} … (hB : B = 0) (hD : D = 0) (hl : l = 0)
    (hbeta : beta = 0) (hdelta : delta = 0) (hzeta : zeta = 0) (htheta : theta = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative (degreeZeroPrimitiveCubic610 …) = Polynomial.C (j / t)) : False := by
  rw [degreeZeroPrimitiveCubic610_eq_flat] at hder      -- :553
  subst hB; subst hD; subst hl; subst hbeta; subst hdelta; subst hzeta; subst htheta
  simp only [degreeZeroPrimitiveCubicFlat610, zero_mul, mul_zero, zero_smul,
             zero_pow, add_zero, zero_add, derivative_zero] at hder
  exact hjdiv (by simpa using (Polynomial.C_eq_zero.mp hder.symm))
```

---

## 4. Assembly

```lean
theorem normalized610ScaleZero_impossible {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) : False := by
  obtain ⟨…, hconeA, hload, hl0, _hb, _hd, _hz⟩ := normalized610ScaleZero_cubicResidual5 hsource
  -- (1) the four odd loads via the N₁ ladder (nested by_cases on cubicN1{Beta,Delta,Zeta,Theta}Top610;
  --     each ¬ branch yields the band inequality by rcases … <;> omega)
  -- (2) the σ-argmin exhaust cubicLoadSigmaSupportCone610_of, one kill per constructor,
  --     allZero by cubicADominant_allLettersZero_impossible
theorem proved_planeKellerNormalized610LowScaleRoute :
    PlaneKellerNormalized610LowScaleRoute (K := K) :=
  planeKellerNormalized610LowScaleRoute_of_scaleZero
    (fun _P _Q _H h => normalized610ScaleZero_impossible h)
```
(`planeKellerNormalized610LowScaleRoute_of_scaleZero`: `Grok610AlignedNonsquareDegreeZeroPrimitiveScratch.lean:1493`; `cases … with` tail as in `Grok610ScaleZeroCubicWallScratch.lean:1856–1930`.)

**Sequencing.** File A (`Grok610ScaleZeroCubicLoadLadderScratch`): §3.1 + §3.2 + §3.6, exporting `normalized610ScaleZero_cubicResidual6` (load-compete, `l = 0`, the four band disjunctions, the σ-cone exhaust). File B: the 12 single-monomial cones. File C: `BC`, `BCE`, `CD`, `BCDE` + assembly.

---

## 5. Honest risks and fallbacks

1. **The `7T = 18a` wall for the N₁-carrier cones (`CD`, `BCDE`).** At equality the N₁ σ-7 face (degree `5a`) ties `7/6912·β·A⁵`. Fallback = the Wall file's N₁/N₂ 2×2 (`n2CubicSigmaFaceBCDE610 = −A · n1CubicSigma7Face610`, `…WallScratch.lean:195` vs `…ADominantScratch.lean:373`): `(7/6912 + 35/41472)·β·a⁷ = (77/41472)·β·a⁷ = 0 ⇒ β = 0`; the other walls: `δ: 7/1152`, `ζ: 35/1728`, `θ: 5/72`; `l`: the proven `143/248832`. Model on `cubicSigmaCone_CD_wall_impossible` (`…WallScratch.lean:362`), `n2CubicSigmaFaceCD610_coeff_top` (:333), `n2CubicLFace610_coeff_top` (:350), `degreeZeroN2Cubic610_natDegree_le` (:147). ≤ 8 extra lemmas, most vacuous by `omega`.
2. **`compute_degree` cost.** Emit pre-substituted rest defs per band; budget `maxHeartbeats 64000000` as at `…LoadCompeteScratch.lean:254`.
3. **The exhaust is the biggest file** (~970 lines at `…WallScratch.lean:866–1834`); split into a 16-way `by_cases` on `{B,C,D,E} = 0` first.
4. **`X ≠ 0` vs `0 < X.natDegree`.** `X ≠ 0` chosen because `T ≥ 9a` contains chambers with a nonzero *constant* `B`; alternatively add `T_S < 9a` to the cones and carve out the flat corner as a 16th constructor (on it `7T ≥ 63a > 54a` kills all odd loads; same three-term face).
5. **CAS re-runs before Lean:** re-run `derive_610_scale_zero_cubic_adominant.py` with the enumeration enabled (the checked-in json has `"enumeration": {"skipped": true}`); extend `derive_610_scale_zero_cubic_wall_mixed.py` to emit per `(S, band)` the rest records and the exact `omega` inequality list; assert in CAS the band bounds `9/2, 15/2, 21/2, 27/2, 12` (λ/ο) and `18/7, 30/7, 6, 54/7` (N₁).
6. **No shortcuts**: single-monomial `mul_ne_zero`, the three proven `ring` identities (`:876`, `:1740`, `:2870`), or `natDegree` contradictions. Axioms stay `propext, Classical.choice, Quot.sound`.
7. **Residual honesty.** If an `(S, band)` rest bound refuses, export `normalized610ScaleZero_cubicResidual6` naming exactly that `(S, band)`.
