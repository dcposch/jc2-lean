**Status:** definition-only phase-2 layer; not yet submitted to Palomar.

# jc72108-depth-witness

Lean 4 / Mathlib definitions for stating finite depth-window survival on the
`(72,108)`, total-defect-6 residue-A chart over `ZMod 105337`.  This project is
a sibling of `theorem-a/` and `vertex-gap/` and uses their toolchain and
Mathlib pins byte-for-byte.

The central proposition is

```lean
JC72108.DepthWitness.HasDepthWitness (D : ℕ) : Prop
```

It means that there is residue-A branch data over `ZMod 105337` satisfying
the fixed radical/chart equations, B-freezing and all six no-log pins, the
four slot-zero gates, and every Jacobian row with `k < D`.  Campaign depths
are restricted to odd `D` with `21 ≤ D ≤ 42`; the upper bound records the
source fact that rows `0..41` are pure y-side data and prevents this layer
from silently making claims after x-side coefficients enter.

No nonemptiness theorem is asserted yet.  In particular, `Solution.lean` is
intentionally only a placeholder importing the checked definitions.  This
keeps the D25 computation from being prejudged.

## Definitional fidelity plan

The formal statement follows the unreduced mathematical object, not its very
large Gröbner presentation.

1. `TemplateVertex`, `LadderDatum`, and `towerTerm` record the template chain,
   exponent table, and approximate-root recurrence
   `h_(j+1) = h_j^k_j - s_j (f-a)^l_j`.
2. `RadicalPoint` retains the 36-fiber variables and the seven literal
   radical/localization equations of the unsplit CORE2 object.  The fixed
   split embedding is kernel-checked at `p = 105337`.
3. `ResidueAData` and `orbitCoefficient` encode the exact nine-orbit registry:
   three f-orbits of total size 126 and six g-orbits of total size 189, with
   orbit sizes 42 or 21, shared stretch/merge coefficients, B-freezing,
   even-support 21-orbits, and PIN42.
4. `throughFactor`, `offFactor`, `orbitFactors`, and `jetProduct` construct
   `Phi` and `Gamma` as the source's finite phase-twisted Cauchy products.
   Each orbit is expanded as seven directions times six or three subbranches;
   no coefficient polynomial is pasted into Lean.
5. `jacobianRow` is the displayed recurrence

       Row_k = sum_(i+j=k) ((i-12) F_i G'_j - (j-18) G_j F'_i),

   with target `-42` at `k=20` and zero elsewhere.  Consequently D21 means
   rows `0..20`, D23 adds `21,22`, and D25 adds `23,24` by definition.
6. `DepthExtension`, `D23Extension`, and `D25Extension` require a larger
   window to agree with the smaller branch data below the exact dependency
   cutoff.  The D23 and D25 tail/frontier names and eta supports are retained
   as metadata, while the conditions themselves remain the same row
   recurrence.
7. CORE2's 22 pivots, 38 residual labels, 18 remaining template coordinates,
   and `27 vars / 45 equations` census are recorded for certificate
   translation.  They do not replace the definition of the window: CORE2 is
   an equivalence-preserving computational presentation of it.

This choice is deliberate.  A future certificate may prove the row equations
from concrete coefficient tables or from a checked pivot trace, while the
human-facing Challenge remains small and tied to the mathematical recurrence.
See [FIDELITY.md](FIDELITY.md) for the declaration-by-declaration source map.

## Verdict-dependent final statements

The final theorem package depends on the D25 result:

| D25 branch | Intended final Lean statement at this scope | What it does not say |
| --- | --- | --- |
| NONEMPTY, with an extracted `ZMod 105337` point | `HasDepthWitness 25` (normally accompanied by `HasDepthWitness 23`) | No inverse-limit point, formal germ, characteristic-zero germ, or Keller pair follows from a finite window. |
| EMPTY on every one of the 36 fibers, with a checked elimination certificate | `HasDepthWitness 23 ∧ ¬ HasDepthWitness 25` | This is a chart-local modular finite-depth kill, not a characteristic-zero theorem and not a statement about other charts or embeddings. |

A proper/nonunit ideal over an algebraic closure is not by itself a proof of
`HasDepthWitness D`, because the present proposition asks for an actual point
over `ZMod 105337`.  The NONEMPTY branch therefore needs a reconstructed
F_p-rational witness.  If only an extension-field point is available, the
coefficient scope must be generalized explicitly rather than silently
identifying algebraic-closure nonemptiness with F_p-rational nonemptiness.

## Layout (Palomar conventions)

| File | Role |
| --- | --- |
| `Challenge.lean` | human-auditable definitions and the parameterized existence proposition |
| `Solution.lean` | verdict-waiting placeholder; no nonemptiness proof yet |
| `FIDELITY.md` | declaration-to-source map and scope boundaries |
| `comparator.json` | planned Comparator surface |
| `formalization.yaml` | phase-2 metadata and review status |
| `scripts/check_axioms.sh` | kernel axiom audit of the proved coefficient lemmas |

Toolchain: Lean `v4.34.0-rc1`, Mathlib revision
`20bc12820422504f9e52ee6caebf8182a9015336`.  The `lean-toolchain`,
`lakefile.toml`, and generated `lake-manifest.json` are byte-identical to both
finished sibling projects.

## Build and check

```sh
lake exe cache get
lake build
./scripts/check_axioms.sh
```

The implementation is kernel-only.  It contains no `native_decide`, custom
axiom, or witness `sorry`; the small modular identities use ordinary kernel
`decide`.

## Scope

Formalized here: the cited template/lattice data, the fixed mod-p coefficient
setup, the exact residue-A orbit-generated jets, the D21 recurrence and its
D23/D25 structural extensions, CORE2/frontier metadata, and the parameterized
existence proposition.

Not formalized here: expanded CORE2/Row_22/Row_24 polynomials, the proof that
the pivot presentation is equivalent to the unreduced rows, a concrete D23 or
D25 witness, Gröbner certificates, inverse-limit compatibility, valuation-e
or Hensel conditions, characteristic-zero lifting, or the global chart cover.

## Provenance and review

Definitions implemented by OpenAI Codex under the campaign's Lean-delegation
workflow.  Source fidelity is awaiting the separate Grok review; all current
Lean declarations and coefficient checks are accepted by the pinned Lean
kernel.
