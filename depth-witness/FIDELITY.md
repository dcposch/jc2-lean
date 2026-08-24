# Definitional fidelity map

This file maps every hand-written declaration in `Challenge.lean` to the
informal source or identifies it as formalization infrastructure. Source line
numbers refer to the parent campaign working tree as of 2026-08-20; the cited
campaign paths are relative to that repository and now begin with `ladder/` or
`cases/`.

The primary sources requested for this layer are:

- `ladder/SHEET6-TEMPLATE.md` §0 and §1a (lines 33–80);
- `ladder/SHEET6-DIRECTIONB.md` header/gauge and §§0–1 (lines 22–92);
- `ladder/SHEET6-DIRECTIONB.md` §7.S3 (lines 1091–1140).

The same sheet's §§7, 8, 8.S, and 9 supply the explicitly requested no-log,
D23, and D25 extension data.  Exact orbit-registry details referenced by the
sheet live in `cases/r1_experiment.py`; those implementation references are
listed rather than pretending the prose prints every branch coefficient.

## Campaign and coefficient declarations

| Lean declaration | Informal source | Fidelity note |
| --- | --- | --- |
| `newtonDegreePair` | campaign target stated by the task; `jc72108/plan-72-108.md` lines 1–4 | Stored as the campaign label `(72,108)`.  It is deliberately not identified with the template's chart degrees `(168,252)`; some source conventions order `(deg P,deg Q)` oppositely. |
| `totalDefect` | `ladder/SHEET6-TEMPLATE.md` lines 61–64 | Literal `td=6`. |
| `templateType` | Template lines 61–62 | Literal `(alpha,beta)=(2,3)`. |
| `fExponentPair` | Template lines 61–63 | Literal `(k_f,l_f)=(126,42)`. |
| `gExponentPair` | Template lines 61–63 | Literal `(k_g,l_g)=(189,63)`. |
| `degreeFMinusA` | Template line 62 | Literal `deg(f-a)=168`. |
| `degreeG` | Template line 62 | Literal `deg g=252`. |
| `poleCharges` | Template lines 62–63 | The displayed `3+3` decomposition of total defect. |
| `commonRamification` | Template lines 63–64 | Literal common root `kappa=42`. |
| `windowPrime` | DirectionB §7.S2–§7.S3, especially lines 1053–1058 and 1099–1111 | Fixed at `105337`. |
| `Coeff` | requested mod-p setup; DirectionB split-prime runs | Definitionally `ZMod windowPrime`. |
| `windowPrime_prime` | arithmetic fact required by the mod-p setup | Kernel proof that `105337` is prime. |
| `windowPrimeFact` | Lean infrastructure for the field instance | Packages `windowPrime_prime` as `Fact`; no extra mathematical hypothesis. |
| `sqrtThree` | fixed embedding used by the CORE2/atlas artifacts; `cases/r1_fullcore.py` lines 136–165 | Literal residue `795`. |
| `zeta42` | same fixed embedding; `cases/r1_fullcore.py` lines 136–165 | Literal residue `2779`. |
| `etaB` | same fixed embedding; `cases/r1_fullcore.py` lines 136–165 | Literal residue `24069`; this is the B-root called `EB` in code. |
| `fLead` | DirectionB lines 54–57 and 86–92; `cases/r1_experiment.py` lines 351–355 | Residue `51107`, representing `7^12/2^6`. |
| `gLead` | same | Residue `33066`, representing `-7^18/2^9`. |
| `sqrtThree_sq` | defining law `r3^2=3` in the emitted radical setup | Kernel check of the fixed residue. |
| `zeta42_pow` | primitive-root setup in `cases/r1_fullcore.py` lines 156–158 | Kernel check of `zeta42^42=1`. |
| `zeta42_primitive` | same | Checks the source's three proper divisor tests `6,14,21`. |
| `etaB_seventh` | `cases/r1_fullcore.py` lines 138,161 | Kernel check of `2*etaB^7=3`. |
| `fLead_value` | DirectionB lines 54–57, 86–90 | Division-free equality `fLead*2^6=7^12`. |
| `gLead_value` | same | Division-free equality `gLead*2^9=-7^18`. |
| `lead_tower_relation` | DirectionB lines 86–92 | Kernel check of `gLead^2=fLead^3` in the `s0=1` gauge. |

## Template ladder and tower

| Lean declaration | Informal source | Fidelity note |
| --- | --- | --- |
| `TemplateVertex` | Template §0, lines 35–43 | Constructors are `R,F_s,G_m,P_1,P_2` with readable Lean names. |
| `QDatum` | Template lines 45–46 | Record for the five displayed entries of `Q(F)`. |
| `LadderDatum` | Template §1a, lines 66–80 | Record for `pi,kappa,d_F,d_g,d_h1,d_h2,D_g` and the exact/lower-bound tower depth. |
| `towardRoot` | Template lines 35–43 | Encodes `P_i -> G_m -> F_s -> R`; the two poles share the merge. |
| `ladderDatum` | Template lines 45–46 and table lines 69–80 | Literal table.  `M_R` and exact root tower depth remain `none`, reflecting the source rather than inventing values. |
| `TowerStep` | Template lines 47–53 | Data `(k_j,l_j,s_j)` for one approximate-root step. |
| `towerTerm` | Template lines 50–53 | Exact structural recurrence `h_0=g`, `h_(j+1)=h_j^k_j-s_j(f-a)^l_j`. |
| `knownTowerExponents` | Template lines 77–80 and the pinned `(3,4)` discussion | Records `(2,3),(3,4),(7,23)` and leaves later steps unspecified. |

## Orbit registry and branch coefficients

| Lean declaration | Informal source | Fidelity note |
| --- | --- | --- |
| `Orbit` | `cases/r1_experiment.py` lines 357–406, referenced throughout DirectionB's window build | Exactly `P1,P2,B,Gp1,Gp2,G0p1,G0p2,GB42,GB21`. |
| `orbitSize` | same, lines 357–403 | Six size-42 and three size-21 orbits exactly as registered. |
| `fOrbits` | same, line 406 | `P1,P2,B`, total size 126. |
| `gOrbits` | same, line 406 | Six g-orbits, total size 189. |
| `isAside` | same, lines 501–529 and 543–570 | Marks precisely the six level-12-one orbits whose `k=0` factors pass through the distinguished direction. |
| `RadicalPoint` | DirectionB §7.S3 and emitted CORE2 header; `cases/directionb_core2_p105337.ms` line 1 | The nine unsplit radical/localization variables after fixing `r3,zeta,EB`. |
| `RadicalPoint.Valid` | last seven equations of the unsplit CORE2 emission; DirectionB §7.S3 lines 1103–1127 | Two cube laws, two `HW/W` laws, two W inverses, and the `alpha1-alpha2` inverse.  Lean names `alpha1/alpha2` are the source's emitted `A1/A2`, not Template's merge directions `a1/a2`. |
| `ResidueAData` | DirectionB chart/window data; exact registry in `r1_experiment.py` lines 357–403 | Shared stretch/merge values plus a uniform infinite tail function.  Only finitely many coefficients are read at a fixed depth. |
| `BFrozen` | DirectionB scope of the D21/D23/D25 objects; §7 level-42 table lines 762–776 | States the B, GB42, and GB21 representative tails are zero. |
| `NoLogPins` | DirectionB §7, lines 711–797 | Exactly the six live level-42 pins. |
| `prefixCoefficient` | DirectionB lines 44–49 | Exact prefix arc at levels `12,18,24,30`. |
| `orbitCoefficient` | `r1_experiment.py` lines 373–403 | Exact fixed levels, shared `uf/vf`, `W/HW`, ordinary tails from 38, even G0 support, B-freeze, and PIN42.  Ignored raw tail fields at forbidden slots do not enter the generated series; `BFrozen`/`NoLogPins` additionally normalize the named chart data. |

## Jet construction and window recurrence

| Lean declaration | Informal source | Fidelity note |
| --- | --- | --- |
| `Jet` | DirectionB §0, `Phi=sum F_s t^s`, `Gamma=sum G_s t^s` | Coefficient function `Nat -> Polynomial Coeff`. |
| `jetOne` | formalization infrastructure | Unit for coefficientwise formal power-series multiplication. |
| `jetMul` | direct-product construction in `r1_experiment.py` lines 409–430 | Exact Cauchy convolution; no truncation or coefficient expansion is hidden. |
| `jetProduct` | direct factor product in `r1_experiment.py` lines 501–541 | Finite recursive Cauchy product. |
| `twistedCoefficient` | `r1_experiment.py` lines 339–342 and 519–537 | Phase action `zeta^(phase*level)`.  The code reduces the exponent mod 42; the Lean value is equal because `zeta42_pow` holds. |
| `throughFactor` | `r1_experiment.py` lines 522–527 | Exact `eta - Y_tilde` factor normalized at level 32. |
| `offFactor` | same, lines 528–537 | Exact `P_arc-C_phase Y + eta*t^20` factor. |
| `orbitFactors` | same, lines 515–538 | Seven directions and `orbitSize/7` subbranches, with `phase=k+7j`. |
| `orbitJet` | same | Product for one orbit. |
| `phi` | DirectionB lines 51–57; f registry | Product over the three f-orbits. |
| `gamma` | same; g registry | Product over the six g-orbits. |
| `mergePolynomial` | Template lines 99–105; DirectionB lines 54–57 | `(eta^3-(3+r3))(eta^3-(3-r3))` in gauge `sigma=6`. |
| `expectedPhi0` | DirectionB lines 54–57 and 86–90 | `fLead * mergePolynomial^2`. |
| `expectedGamma0` | same | `gLead * mergePolynomial^3`. |
| `TopConditions` | DirectionB §1, lines 86–92, plus §0 line 82–84 | The two top-polynomial identities, tower cancellation, and Row_0 gate. |
| `jacobianRow` | DirectionB §0, lines 58–66 | Verbatim coefficient recurrence with integer weights `(i-12)` and `(j-18)`. |
| `rowTarget` | DirectionB lines 60–66; residual convention lines 610–644 | `C(-42)` only at row 20, zero otherwise; equivalent to emitted `Row20+C(42)=0`. |
| `WindowConditions` | DirectionB D21 window plus §7 pins | Radical chart, B-freeze, no-log, top gates, and every row `k<D`. |
| `IsCampaignDepth` | D21/D23/D25 ladder; DirectionB lines 68–73 | Odd `D>=21`; `D<=42` is a fidelity guard because only rows 0–41 are certified pure y-side. |
| `HasDepthWitness` | requested Palomar statement template | Literal existential over `ResidueAData` in `ZMod 105337`; no theorem asserting it is included. |
| `TruncatesTo` | D25 structural finding at DirectionB lines 1984–1987 and general depth truncation | Agreement through absolute level `<32+lower`, the largest source level that can affect slots `<lower`. |
| `DepthExtension` | `DEPTH-STAB.md` depth ladder and DirectionB §§8–9 | Requires both windows, ordered campaign depths, and truncation agreement. |
| `D23Extension` | DirectionB §8, especially lines 848–918 and 1166–1181 | Specialization `21 -> 23`. |
| `D25Extension` | DirectionB §9, especially lines 1950–2000 | Specialization `23 -> 25`. |

## CORE2 and deep-frontier metadata

| Lean declaration | Informal source | Fidelity note |
| --- | --- | --- |
| `RowCell` | row/cell notation throughout DirectionB | Pair `(row, eta exponent)`. |
| `rowCellFamily` | structural support pattern of the emitted rows | Generates arithmetic progressions with step 3. |
| `d21RawCells` | DirectionB §6 window ledger; `directionb_residual32.rows.txt` lines 78–154 | All 77 raw cells before PIN42 makes `(10,28)` redundant. |
| `core2ResidualCells` | DirectionB §7.S3; `directionb_core2.rows.txt` residual legend | Exactly the 38 post-pivot labels.  They are not asserted to be raw coefficients. |
| `CoreCoordinate` | DirectionB §7.S3 lines 1107–1127; `fastelim.py` lines 426–429 | Exactly the 18 remaining template coordinates. |
| `coreCoordinateValue` | same | Reads each named coordinate from `ResidueAData`. |
| `PivotCoordinate` | DirectionB §7.S3 lines 1099–1104 plus the banked 16-high pivot trace | Exactly 16 high and six low pivot variables. |
| `pivotCell` | `directionb_core23_elim.py` lines 6–11; `d25_assemble.py` lines 140–151 | Exact variable-to-row-cell map.  Elimination order and expanded pivot rows are intentionally outside scope. |
| `core2VariableCount` | DirectionB §7.S3 lines 1107–1111 | Literal 27. |
| `core2EquationCount` | same | Literal 45 = 38 residual plus seven radical/chart equations. |
| `core2PivotCount` | DirectionB lines 1099–1104 | Literal 22. |
| `core2ResidualCount` | DirectionB lines 1107–1111 | Literal 38. |
| `core2TemplateCoordinateCount` | same | Literal 18. |
| `D23Tail` | DirectionB lines 1166–1172 and corrected deep-label registry in the D23/D25 assembly | Ten Row_22 affine-tail names in canonical order. |
| `d23EtaSupport` | DirectionB §8; D23 emitter | `{1,4,...,28}`. |
| `D25Frontier` | DirectionB §9 lines 1961–1979; D25 assembly frontier | Ten Row_24 frontier names in canonical order. |
| `d25EtaSupport` | DirectionB lines 1961–1969 | `{2,5,...,26}`. |

## Known scope boundaries

- This layer defines the unreduced orbit-generated window.  It records but
  does not formalize the proof that CORE2 pseudo-division and W-unit stripping
  preserve that window's solution set.
- It does not include expanded polynomial lists, Gröbner bases, normal-form
  traces, or witness coordinates.  Those are certificate payloads for the
  verdict-dependent Solution.
- `HasDepthWitness D` asks for an F_p-rational point.  “Proper ideal over the
  algebraic closure” is weaker and cannot fill this theorem without an actual
  `ZMod 105337` point or an explicit generalization of the coefficient field.
- D25 NONEMPTY gives only finite-window survival.  D25 EMPTY gives only the
  scoped modular chart kill described in DirectionB §9; neither branch alone
  proves a characteristic-zero or global Jacobian statement.
- No known source datum in the requested scope has been strengthened or
  silently filled in: `M_R` and the exact root tower depth remain unresolved.
