# Maximum partial `y`-degree eleven for plane Keller pairs

Lean 4 / Mathlib formalization.  **Statement proved.**  Let `K` be an
algebraically closed field of characteristic zero.  If `P, Q ∈ K[x,y]` have
constant nonzero Jacobian and both have actual partial `y`-degree at most
eleven, then `K[P,Q] = K[x,y]`.  The proof assumes exactly two cited classical
theorems, stated as explicit hypotheses of the Lean theorem:

- `PlaneKellerPrimeTotalDegreeGCDRoute`: a Keller pair whose total-degree gcd
  is prime generates (Nagata 1989, Theorem 7.3, coordinate-free total-degree
  form);
- `PlaneKellerStandardEndpointGCDObstruction`: the standard-pair endpoint
  obstruction (Guccione--Guccione--Valqui 2017, Corollary 7.9).

Headline declaration (module `Max11Solution`, file
`Max11UnconditionalAssemblyScratch.lean`):

```lean
theorem Max11DegreeRoutes.Max11PlaneKellerGenerationWithClassicalInterfaces
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (hendpoint : PlaneKellerStandardEndpointGCDObstruction (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      MvPolynomial.degreeOf 1 P ≤ 11 → MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q
```

`IsPlaneKellerPair P Q` means the `MvPolynomial.pderiv` Jacobian is a nonzero
constant; `PlanePairGenerates P Q` means `Algebra.adjoin K {P, Q} = ⊤`;
`degreeOf 1` is the actual partial `y`-degree.

## Field hypothesis

Every theorem in this project carries the binders
`{K : Type*} [Field K] [CharZero K] [IsAlgClosed K]`.  Algebraic closure is
used inside the low-scale leaves (for instance to write a nonzero common core
as `H = h^2` at `(4,6)`).  Nothing is proved for fields of characteristic zero
that are not algebraically closed, and no scalar-extension descent is
formalized.  This is the one substantive narrowing relative to the informal
source, which states its theorem for characteristic-zero fields.

## What is proved, and what is not

Proved (kernel-checked, no `sorry`, axioms `propext`, `Classical.choice`,
`Quot.sound` only):

1. The finite degree-routing certificate through eleven: route classification,
   uniqueness of the primitive pair `(6,9)`, recursive closure for an abstract
   symmetric predicate, and the frontier checksum at twelve.
2. Its instantiation for actual bivariate polynomials, including the
   zero-degree, equal-degree, and divisibility Keller routes.
3. Reduction of coprime partial degrees, of odd common scale at gcd two, and
   of the nondivisible `(6,9)` route to the prime-total-degree-gcd hypothesis
   by exact source shears and Dirichlet's theorem; the divisible `(6,9)` core
   is discharged by the imported sibling exclusions.
4. At gcd two with even common scale: the endpoint obstruction removes every
   scale above two; UFD extraction and target rescaling normalize the five
   primitive pairs `(4,6)`, `(4,10)`, `(6,8)`, `(6,10)`, `(8,10)` to literal
   common scales `0` and `2`.
5. All ten normalized low-scale cases are excluded internally.  No low-scale
   case remains open.

Not proved here: the two classical theorems themselves; descent to arbitrary
characteristic-zero fields; the plane Jacobian conjecture beyond partial
`y`-degree eleven; the strong arbitrary-pair twice-prime statement (GGV 2017
proves it only for the globally minimal counterexample gcd, and it is not used).

## Comparator configurations (one Palomar entry each)

This package carries seven Comparator configurations at one commit.  Each
registry entry certifies exactly the `theorem_names` in its own comparator
file and nothing else.  The challenge module for all of them is
`Max11Challenge`.

| Comparator file | Solution module | Certifies |
|---|---|---|
| `comparator.json` | `Max11Solution` | the unconditional headline above (40 theorems, including the supporting results) |
| `comparator-conditional.json` | `Max11Assembly` | the same composition with the five leaf routes as additional explicit hypotheses (35 theorems); registered separately only because the unconditional closure exceeds the verifier's single-run budget, and to be read together with the leaf entries |
| `comparator-leaf46.json` | `LowScale46ScaleTwo` | `proved_planeKellerNormalized46LowScaleRoute` and `proved_planeKellerNormalized46ScaleTwoRoute`: every normalized `(4,6)` leading-core source at scale `0` or `2` generates |
| `comparator-leaf410.json` | `Grok410ChainPromotionScratch` | `planeKellerNormalized410LowScaleRoute_proved` |
| `comparator-leaf68.json` | `Grok68TerminalZeroMeetingCellScratch` | `proved_planeKellerNormalized68LowScaleRoute` |
| `comparator-leaf610.json` | `Grok610ScaleZeroCubicLoadWallsScratch` | `proved_planeKellerNormalized610LowScaleRoute` |
| `comparator-leaf810.json` | `Grok810RouteClosureScratch` | `proved_planeKellerNormalized810LowScaleRoute` |

A leaf entry, for example the `(4,6)` configuration, certifies only its own
leaf theorem(s) over an algebraically closed field of characteristic zero; it
says nothing about the other four pairs, the classifier, or the headline.
Those are separate configurations at the same commit.

## Sources and originality

The finite composition follows the routing rules of the frozen campaign report
shipped under `sources/`.  The source-shear bridge from partial `y`-degree to
the two total-degree theorems, the gcd-two normalization, and all five
low-scale leaf exclusions are original to this formalization; they are not
translations of the report or of the cited papers.  See `formalization.yaml`
(`sources`, `fidelity`, `alignment`) for the exact correspondence.

## Automation disclosure

The Lean development was produced with agent assistance throughout: OpenAI
Codex agents (core definitions and early modules, credited in the headers of
`Max11Core.lean`, `Max11Challenge.lean`, `Solution.lean`, `CubeCore.lean`, and
as gpt-6-astra the `Astra*` modules of the `(8,10)` leaf), xAI Grok 4.6
(`Grok*` leaf proof modules), and Claude Opus 5 / Claude Fable 5.1 (planning,
`Fable*` modules, package assembly, verification-cost engineering).  Every
proof is kernel-checked.  Human direction, review of the statements, and
responsibility for publication: Dan Clemens Posch.  Details in
`formalization.yaml` under `automation`.

## Verification

```sh
lake build                       # all modules; toolchain pinned in lean-toolchain
lake env lean Max11Solution.lean # the unconditional headline module
```

For the axiom report of a comparator theorem, e.g. the `(4,6)` leaf:

```lean
import LowScale46ScaleTwo
#print axioms Max11DegreeRoutes.proved_planeKellerNormalized46LowScaleRoute
```

Measured on a 4 vCPU / 16 GiB replica of the Palomar runner: the `(4,6)`
closure builds in under 1 h 20 min; the unconditional headline closure (2,585
modules) takes about 7 h 30 min and is the reason the conditional and leaf
configurations exist.

## Licence

Apache-2.0; see `LICENSE`.
