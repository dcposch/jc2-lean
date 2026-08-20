# SUBMISSION.md — what DC must do (nothing here is automated)

PUSHED 2026-08-19: repo github.com/dcposch/jc2-lean (public, branch master), project path `theorem-a`, commit c59d6ef0d5ea85707d78980ea03c38608285d446.

Status when this file was written: `lake build` green on Lean v4.34.0-rc1 +
Mathlib master 20bc1282...5336; `scripts/check_axioms.sh` passes (both theorems use only
`propext`, `Classical.choice`, `Quot.sound`); no git repo initialized yet, by
design.

## 1. Create the public GitHub repo and push

```sh
cd /Users/dc/code/math/jc72108-lean
git init -b main
git add .gitignore Challenge.lean Solution.lean LICENSE README.md \
  SUBMISSION.md comparator.json formalization.yaml lake-manifest.json \
  lakefile.toml lean-toolchain scripts/check_axioms.sh
git commit -m "Theorem A (ODE rigidity) formalization for Palomar"
gh repo create dcposch/jc72108-lean --public --source . --push
# (or create empty repo on github.com, then: git remote add origin ... && git push -u origin main)
```

Notes:
- `.lake/` is gitignored; do NOT commit it.
- `lake-manifest.json` MUST be committed (Palomar wants pinned deps).
- Optional: delete this SUBMISSION.md before the submission commit if you
  don't want process notes in the snapshot (it is harmless either way).

## 2. Copy the exact commit SHA

```sh
git rev-parse HEAD
```

Copy the full 40-character SHA. Palomar reviews that immutable snapshot only;
anything uncommitted or pushed later is invisible to it.

## 3. Submit

Open <https://submit.palomar-registry.org/> and:

1. Enter repository `dcposch/jc72108-lean` and the full commit SHA.
2. Leave the project / Comparator-config / metadata path fields blank
   (root layout, conventional file names).
3. Authorization question: you are the responsible author/maintainer of the
   substantive formalization (this repo is NOT a thin wrapper).
4. Prove write access via the GitHub sign-in route (browser). The
   tag+gist route is for agents and is deliberately weaker.
5. **Keep the status-page link.** Palomar does not email and has no accounts;
   that link is the only way back to the submission.

## 4. After mechanical verification

- Mechanical verification runs publicly (GitHub Actions); the editorial
  review appears on your private status page, target within ~1 hour.
- Nothing is registered until you explicitly choose "register" on the status
  page. Registration is permanent (append-only registry, versioned
  Palomar ID). Withdrawing pre-registration leaves no public registry trace.
- If review requests changes: fix, commit, push, and submit the NEW SHA (a
  review is tied to one immutable commit).

## What was verified locally (2026-08-19)

- `lake build` — clean (both `Challenge` and `Solution` targets).
- `./scripts/check_axioms.sh` — output:
  `'TheoremA' depends on axioms: [propext, Classical.choice, Quot.sound]`,
  same for `TheoremA_charP`, then `OK`.
- Challenge.lean is well under Palomar's preferred 300-line / 32 KiB
  reviewing surface; imports are Mathlib-only.
- comparator.json follows the PalomarTemplate format
  (`challenge_module` / `solution_module` / `theorem_names` /
  `definition_names` / `permitted_axioms` / `enable_nanoda`) — note this is
  the actual registry format, not the `{"compare": [...]}` sketch from the
  campaign notes.
- formalization.yaml follows the v0.4 template schema with the agreed
  metadata: name `jc72108-theorem-a`, author Dan Clemens Posch, Apache-2.0,
  source-based (campaign theory bundle doi:10.5281/zenodo.22002825,
  MATHIEU.md §§5.1/5.4 = formalizes; vertex-gap artifact
  doi:10.5281/zenodo.21894922 = background, software/MIT; Żołądek 2008
  Appendix A.7 = background with directional note, no DOI given;
  Hermoso–Alcázar arXiv:2410.18867 = independently-proves), arXiv
  `math.AG`+`math.AC`, MSC `14R15`, automation agent+manual with AI-roles
  narrative, honest review status (self-assessed + campaign-internal AI
  fidelity review, no external peer review).
- Semantic-fidelity review (Sol, `xmodel/sol-lean-fidelity.md`, 2026-08-19):
  verdict FAITHFUL on both Lean statements.  Its attribution fixes are
  incorporated: the ODE theorem is cited by label (`thm:ode`, "ODE rigidity,
  all weights", Theorem 6.1 in the current compilation — NOT 6.5, which is
  the unformalized block-variety theorem `thm:R`); the campaign source is
  the theory bundle 10.5281/zenodo.22002825 (MATHIEU.md §5.1); the wrong
  Żołądek DOI was removed; `TheoremA_charP` is described as a standalone
  strengthening extracted from the Section 6 proof.
