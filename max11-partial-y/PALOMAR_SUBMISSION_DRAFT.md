# Max-11 Palomar submission — prepared deltas (apply when the three leaf routes are closed)

## Preconditions (all must be kernel-green and committed on origin/master)
- `proved_planeKellerNormalized68LowScaleRoute`, `proved_planeKellerNormalized610LowScaleRoute`,
  `proved_planeKellerNormalized810LowScaleRoute` (route closure scratch files), and the headline
  `Max11PlaneKellerGenerationWithFourNormalizedRoutesAfterClosed410 hprime hendpoint
   proved_46 proved_68 proved_610 proved_810` re-exported as the final theorem
  (working name `Max11DegreeRoutes.Max11PlaneKellerGenerationWithClassicalInterfaces`,
  premises exactly `PlaneKellerPrimeTotalDegreeGCDRoute` and `PlaneKellerStandardEndpointGCDObstruction`).
- Promotion: `python3 scripts/coord/promote_closure.py <final module>` reports 0 untracked and
  0 non-green modules; add every listed module to `lakefile.toml` roots and import the final
  module from `Max11Assembly.lean`; full box build green; `#print axioms` = propext /
  Classical.choice / Quot.sound only.

## Package
`python3 scripts/coord/build_max11_package.py --src max11-partial-y --comp gcd3-69-composition --out ../max11`
(validated 2026-09-02: 641 modules, 9387 jobs, standard axiom trio). The package must contain the
composition modules as sources (Comparator sandbox forbids sibling srcDir libs).

## formalization.yaml deltas
- `project.description`: replace the last two sentences with: "All five primitive gcd-two leaves
  are now closed internally; the only remaining inputs are the canonical prime-total-degree-gcd
  theorem and the published standard-endpoint obstruction, both cited as explicit hypotheses."
- `status.scope`: state that maximum partial y-degree eleven follows from those two cited results
  and nothing else; keep the sentence that the plane Jacobian conjecture itself is not claimed.
- `status.main_results`: prepend the final theorem (file `Max11Assembly.lean`, sorry_count 0,
  axioms the standard trio) and the three `proved_planeKellerNormalized{68,610,810}LowScaleRoute`.
- `related_formalizations`: keep PALOMAR-2026-08-25-000002 and the gcd3-69 entries; add the
  registered composition id once known.
- `automation.methods`: models = xAI Grok 4.6 (proof lanes), Claude Opus 5 (planning), Claude
  Fable 5.1 (coordination); frameworks = grok CLI, Claude Code.

## comparator.json deltas
- `theorem_names`: add the final theorem and the three `proved_planeKellerNormalized*LowScaleRoute`.
- `definition_names`: unchanged (all route Props are already listed).

## Submit
submit.palomar-registry.org (GitHub sign-in) → upload the package → register from the status page;
record the registry id in README.md "Public progress" and in formalization.yaml.
