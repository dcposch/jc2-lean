# Hostile different-model review — GCD3 `(6,9)` coverage composition

| Field | Value |
|---|---|
| Claim under review | Frozen composition: the reviewed partial-`y` history stop, first common-cubic split, aligned lower-Pfaffian exclusion (with target-translation erratum), cube-mismatch Faber–Laurent landing, and cube trajectory closure compose disjointly and exhaustively; (A) no characteristic-zero Keller pair of actual `y`-degrees `(6,9)` with `3\|H` exists; (B) every characteristic-zero Keller pair with maximum actual `y`-degree at most eleven is a polynomial automorphism; frontier checksum at maximum twelve is exactly `(8,12),(9,12)` |
| Overall verdict | **CONFIRMED** at the stated scope, with one explicitly quarantined process limitation (byte-level regression not re-executed by this reviewer; see “Regression layer”) |
| Smallest failing identity | none |
| Smallest failing handoff | none |
| Smallest exact missing obligation | none mathematical. Two process items, neither of which blocks a numbered claim: (i) this review environment has no shell, so `shasum -a 256 -c` and the composition replay were hand-traced, not executed — the two registered commands remain a one-minute operator obligation on a shell-enabled host; (ii) one ledger dependency, `xmodel/gcd3-69-cube-trajectory-kuranishi-review-grok-20260824.md`, is uncommitted working-tree state at the stated basis (its bytes are hash-pinned by the replay and by this review’s reading; “committed basis” is exact for the other eleven ledger files) |
| Evidence tier | independent hand re-derivation of the `y^{13}` row, depression, all Kummer weights (coefficients, integration constants, and the four lower invariants), the `(omega-1)` inverse, the cube/noncube valuation dichotomy, the Faber translation action `(3.2)`, the `A_n` polynomial parts and `6^5` triangularity, the finite-pole zero/pole-degree count, the `EB=(3/4)X^2(X-3a_4^2)` factorization, the noncube infinity count via `w=h^2q^3` giving degree `r-1`, the `d\neq0` orbit values `(45\pm3\sqrt{195})/2\neq-27/4`, every constant-`s` integrality test, the cusp model `r_5=(27/2)\lambda^7-\nu^2/(1458\lambda^6)` and its two-pole contradiction, the genus-one constancy arguments, both descent arguments, and a complete independent hand enumeration of all 78 unordered / 144 ordered degree pairs with full `D/E` child audits; line-by-line hand trace of `replay.py` including every `consume` set; all twelve producer/review ledger documents read in full |
| Reviewer / model | Claude (Anthropic, Fable 5). Different model family from the producer lane (OpenAI Codex/Sol) and from the leaf reviewer (Grok 4.6, xAI) |
| Repo | `/Users/dc/code/math/jc2` |
| Basis | `1e60fcedc8626650c7c7544ad296c3624173415f` (read textually from `.git/refs/heads/master`; matches the launch prompt) |
| Review date | 2026-08-24, single session |
| Environment | review harness without shell execution (no `git`/`shasum`/`python3` invocation possible; `Monitor` denied by permission mode). Scratch confined to `/tmp/gcd3_69_review_claude/`; no tracked path touched except this report |

Documents reread in full before any verdict: the composition report, `REGISTRATION.md`, `replay.py`, `MANIFEST.sha256`, `FREEZE.sha256`, and all twelve producer/review files of the Section 7 ledger. No producer, case, canonical, ladder, notes, prompt, log, run, or erratum file was edited. No AWS resource was touched. This file is the only write.

---

## Promotion

**Accept the composed verdict at exactly the displayed scope:**

- **(A)** For every characteristic-zero field `k`: there is no Keller pair `P,Q in k[x,y]` with `det J(P,Q) in k^*`, actual partial `y`-degrees `{6,9}`, and `3 | H`, where `H=deg(h)` and `h` is the primitive common leading core of `a_6=alpha h^2`, `b_9=beta h^3`. The class is empty, by disjoint exhaustion of `h` noncube (aligned lower-Pfaffian exclusion) and `h` cube (Faber–Laurent landing plus trajectory closure, separately for `d=-delta/2` nonzero and zero).
- **(B)** For every characteristic-zero Keller pair with `max(deg_y P, deg_y Q) <= 11`: `k[P,Q]=k[x,y]`. This follows from (A) plus the reviewed `Z/G/D/E` routes and a terminating lexicographic recursion whose complete table and child audit are independently reproduced below (78 unordered, 144 ordered pairs).
- The maximum-twelve statement is a **frontier checksum only**: the classifier’s first new primitives are exactly `(8,12)` and `(9,12)`. No maximum-twelve theorem is claimed or licensed.

**Do not promote this to:** an arbitrary-support theorem; a *new* total-degree theorem (a total-degree-`<=11` automorphism statement follows a fortiori from (B) since `deg_y <= deg`, but it is classically known and adds nothing — do not cite this composition as its source of novelty; the genuine content of (B) is the unbounded-`x`-degree partial-`y` statement); any maximum-twelve theorem; a polynomial Keller counterexample; polynomiality of the depression `z=sy+r`; an import of nontrivial-Kummer weight vanishing into the polynomial cube core; a full-cubic boundary reduction; or JC2.

**Smallest valid successors.** (i) Operator regression: run `shasum -a 256 -c cases/gcd3_69_coverage_composition_20260824/FREEZE.sha256` and `python3 cases/gcd3_69_coverage_composition_20260824/replay.py` on a shell-enabled host and confirm the terminal `payload_sha256=d7e030…ecd4`; commit the pinned bytes, including the trajectory review. (ii) Mathematics: the frontier pairs `(8,12)` (`gcd 4`, `12 mod 8 = 4`) and `(9,12)` (`gcd 3`, `12 mod 9 = 3`), each requiring its own landing analogous to Sections 2–4 of the composition. No generic coefficient rectangle and no AWS are licensed.

---

## Quarantine (front)

No result here proves or disproves JC2, exhibits or excludes a Keller pair outside the stated degree classes, or says anything about maximum twelve beyond a checksum. Producer PASS strings were not used as evidence anywhere in this review; every mathematical claim was checked against the reviewed source documents and against independent hand derivations. The byte-level attestation layer (SHA-256 recomputation and replay execution) was **not executed** by this reviewer — the review environment has no shell — and is quarantined as an explicit operator obligation; the hash *graph* was verified consistent across all seventeen documents read, and the replay was hand-traced with no reachable failure path on the pinned bytes. Nothing in the mathematical verdicts depends on that layer.

---

## Scope (not enlarged)

Exactly (A), (B), and the frontier checksum, over an arbitrary characteristic-zero coefficient field by scalar extension and descent, in actual partial `y`-degrees. The leaves are consumed at their reviewed scopes and are not reproved here beyond independent spot re-derivation of every load-bearing identity that the composition routes through.

---

## Headline and subclaim table

| # | Prompt claim | Verdict |
|---|---|---|
| 1 | Exact landing and scope: every consumed premise is emitted upstream; target swaps/scalings and base change preserve actual degrees, boundaries, and `3\|H`; depression is coefficient-field, not a source automorphism | **CONFIRMED** |
| 2 | Field dichotomy cube/noncube is exhaustive, disjoint, and well-posed; polynomial cube root via valuations; constant absorbed exactly where `k=\bar k` supplies cube roots; zero/constant cores handled | **CONFIRMED** |
| 3 | Noncube handoff: `delta=0` derived from weight one, not assumed; exactly and only `c_7,c_5,c_4,c_2,c_1` weight-forced; `c_6,c_0` gauged, `c_3` covariant; input matches the aligned lower-Pfaffian theorem; no illicit imports | **CONFIRMED** |
| 4 | Cube handoff and second partition: no Kummer vanishing imported; complete Faber landing with all constants; `r_1'=\dots=r_4'=0`, `6r_5'=j/s`; finite-pole dichotomy; exhaustive `d\neq0 / d=0`; mixed `rho_3,rho_4` split correct; no omitted case found under targeted search | **CONFIRMED** |
| 5 | Adversarial typing controls: both controls independently re-derived and pass; a control pass alone **cannot** certify mathematical branch typing (they are routing/regression checks, exactly as the report states); the typing itself was verified from the leaf documents | **CONFIRMED** |
| 6 | Degree recursion: independent table equals the producer’s; all `D/E` children audited; measure strictly decreases; 78/144 counts; unique pre-composition primitive `(6,9),3\|H`; frontier-12 exactly `(8,12),(9,12)` | **CONFIRMED** |
| 7 | Field theorem and descent: emptiness descends trivially; automorphy descends by unique inverse / faithful flatness; `H` and actual degrees stable under base change; inseparability vacuous in characteristic zero; swap/scaling edge cases close | **CONFIRMED** |
| 8 | Logical boundary: strongest supported statement is exactly (A)+(B) (+frontier checksum); no leaf is sampled, provisional-without-review, or mismatched; forbidden promotions identified and none is made by the producer | **CONFIRMED** |

---

## Regression layer: what was and was not run

**Not run (environment):** this review session exposes no shell on any channel. `git`, `shasum`, and `python3` could not be invoked; a delegated executor also had no shell, and the one available execution surface (`Monitor`) was denied by the permission system, whose instruction to stop and report was followed. Therefore the two registered commands

```sh
shasum -a 256 -c cases/gcd3_69_coverage_composition_20260824/FREEZE.sha256
python3 cases/gcd3_69_coverage_composition_20260824/replay.py
```

were **not executed by this reviewer**, and no hash in the table below was independently recomputed from bytes. This is a reproducibility note, not a mathematical gap: the checks are regression-only by the registration’s own rules, and the mathematical evidence is the reviewed source documents, all of which were read in full.

**Done instead:**

1. **Hash-graph consistency.** The twelve `EXPECTED_HASHES` entries in `replay.py` are byte-identical to the composition report Section 7 ledger; the trajectory-review hash equals the one displayed in the composition header and in `REGISTRATION.md`; every producer/review file’s internal hash tables (first-gate review, lower-Pfaffian review, erratum review, cube-mismatch review, trajectory review) quote the same values for every shared artifact; `MANIFEST.sha256` is the three-line subset of `FREEZE.sha256`, which adds the manifest’s own hash; the four `FREEZE` entries match the launch prompt, as do the freeze self-hash `9388b4…d87b` and payload `d7e030…ecd4`. No inconsistency anywhere in the DAG.
2. **Basis.** `.git/refs/heads/master` reads `1e60fcedc8626650c7c7544ad296c3624173415f`, matching the launch prompt. Per the session’s git-status snapshot, eleven of the twelve ledger files are committed and clean at that basis; `xmodel/gcd3-69-cube-trajectory-kuranishi-review-grok-20260824.md` is present but untracked (it landed after the last commit), as are the composition report and case directory themselves. The freeze pins all of their bytes by hash; committing them is part of the operator successor.
3. **Replay hand-trace.** `replay.py` was traced line by line. `pin_inputs` fails closed on any byte change. All three route states were traced: every `consume` set is contained in the previously emitted facts (checked set-by-set); `exact_kummer_delta_zero` verifies `(-1+ω)(-2/3-ω/3) = 1` in `Q[ω]/(ω^2+ω+1)` — re-derived by hand: real part `(−1)(−2/3)−(1)(−1/3)=1`, `ω`-part `(−1)(−1/3)+(1)(−2/3)−(1)(−1/3)=0`; the cube control’s `poly_mul` gives `(x^2+1)^3={6:1,4:3,2:3,0:1}` (hand-checked), `max=6`, `6 mod 3=0`; the noncube control’s `h={3:1,2:-3,1:2}` has `h(0)=0`, `h'(0)=2`; the `c7`-retention, ordered-constant-tuple, and Kummer-leak guards are all satisfiable only on the coded paths; `compose_69` requires both partition markers and all three terminals. The degree audit was fully hand-simulated (see the table below): no `RouteFailure` is reachable on the pinned bytes. The payload is deterministic (no time or randomness), so `payload_sha256` is reproducible by the operator command.

### Checked hashes

All values below are transcriptions from the frozen files/prompt, verified mutually consistent across every document that quotes them; none was recomputed from bytes in this environment.

```text
7eda0a469585247479d46c8f5f2ce95d2643ae8541f0d7f9c80e1c8537fffb0c  xmodel/gcd3-69-coverage-composition-20260824.md        (FREEZE, MANIFEST, prompt)
b3d8cdec442d2199bfa973f10d2dcf67fb674cc9d8f359924d69236728a2db85  cases/.../REGISTRATION.md                              (FREEZE, MANIFEST, prompt)
6f255691fa348d0b458933aee01f2cc823298209a6a77ef0863ca06176dde30c  cases/.../replay.py                                    (FREEZE, MANIFEST, prompt)
afe95b5fbd9ad6df3831e3c79a70137be5c5128c158d3a82bae8c761af17ee8a  cases/.../MANIFEST.sha256                              (FREEZE, prompt)
9388b4cdd0b4ded3078cdce07fe1f30b8affd536a7f28c01c8fa914d92dbd87b  cases/.../FREEZE.sha256                                (prompt self-hash)
d7e030685c84e7c7366524e4b28f8516a5bf9d5060c3ebdba3990ca2e243ecd4  canonical replay payload                               (report §8, REGISTRATION, prompt)

6994dd6bc1642122ba549be474d2465203faf554d93da5146ecb212dbaaf89fe  xmodel/as109-partial-y-history-stop-20260824.md
f9d547f0f17dc3557ed8edce19912b4930dc2125542c7f9b3e4782c554a03afd  xmodel/as109-partial-y-history-review-grok-20260824.md
f63bf74fd1013c74645f9f7fe9292db69199572b390b5b19d160c5ed13b373e8  xmodel/gcd3-69-common-cubic-first-gate-20260824.md
5416440bc12bb50ecebfdfa520082aa9e88a26069b43deb13bdaabfcd1690503  xmodel/gcd3-69-common-cubic-first-gate-review-grok-20260824.md
7671785519bf4e55b602f117740bd8d8571c6982a8916235407a2bb0a2263043  xmodel/gcd3-69-lower-pfaffian-successor-20260824.md
a000619d8b5597add21716d525856c459ff57d5a2b2ab75b85de5d9d08970b27  xmodel/gcd3-69-lower-pfaffian-successor-review-grok-20260824.md
43fa36968bb90414748330c1b4a5d5169a0eaa21b1925623764e96204e049c78  xmodel/gcd3-69-target-translation-erratum-20260824.md
f4cb57ca765138ed2decab01b12a7f884c37f9a847d80e90162ee751bb3df837  xmodel/gcd3-69-target-translation-erratum-review-grok-20260824.md
6a2799dfe46828c70462d51a842a3fc0adf0515b8ded7a576cdb837d81847d20  xmodel/gcd3-69-cube-mismatch-gate-20260824.md
2648eef3b8091970655a94743c6c181343a94534b6454f43c579b310331ba7d7  xmodel/gcd3-69-cube-mismatch-review-grok-20260824.md
069f6280332b44d93dcad17801dc7136d4a79fb06ace101c2dce8a4e746b5e7b  xmodel/gcd3-69-cube-trajectory-kuranishi-20260824.md
7bcf18d69344acc2277a0184ca1aeeb717ebad35c3aacf91421874b7e59f5cc9  xmodel/gcd3-69-cube-trajectory-kuranishi-review-grok-20260824.md
```

All six leaf reviews carry overall verdict **CONFIRMED** in their frozen bytes, at charged bases `51aa1cc2…`, `6f2e49e6…`, `1e4480c1…` (three), and `c327bdc8…` respectively, forming the commit chain up to the present basis. The lower-Pfaffian and trajectory producers’ “provisional/conditional” headers are discharged exactly by this chain of confirmations: each conditional input is itself reviewed at or above the point where it is consumed.

---

## Claim 1 — exact landing and scope

**CONFIRMED.**

*Premise emission.* Starting from a Keller pair of actual `y`-degrees `(6,9)`: the history stop derives (1.1) `n a_m' b_n - m a_m b_n' = 0` — independently re-derived as the unique `y^{m+n-1}` contribution of `P_xQ_y - P_yQ_x` — and the UFD consequence `a_6=alpha h^2`, `b_9=beta h^3` (its (3.2)); this is exactly the composition’s charged landing, with the first gate normalizing `alpha=beta=1` by the two constant target scalings `P\mapsto P/alpha`, `Q\mapsto Q/beta` (no root extraction needed). The first gate then emits `s^3=h` over `L=k(x)(s)` and derives the `y^{13}` identity — re-derived here term by term:

```text
8a_6'b_8 + 9a_5'b_9 - 6a_6b_8' - 5a_5b_9'
  = 48s^{13}s'B + 45s^{13}s'A + 9s^{14}A' - 48s^{13}s'B - 6s^{14}B' - 45s^{13}s'A
  = s^{14}(9A'-6B'),
```

so `delta=3A-2B` is a constant of `L`, and the constant field of `L/k(x)` is `k` (finite separable extension of a differential field with constants `k`, `k` algebraically closed). The translation `r=A/6` kills `z^5` and sends the `z^8` coefficient to `B-3A/2=-delta/2` — re-derived on the truncations `(z-r)^6+A(z-r)^5`, `(z-r)^9+B(z-r)^8`. The complete boundary jets `s^\ell f^{(\ell)}(r)/\ell! \in k[x]` (`0<=\ell<=6`, and to `9` for `g`) are exactly the `y^\ell`-coefficients of `P,Q`, hence emitted by source polynomiality; `P_5=6s^5r` was checked (`f^{(5)}/5! = 6z` for a depressed monic sextic).

*Degree/boundary preservation.* Target swap negates `j` (still in `k^*`), permutes the degrees and boundaries; constant target scalings multiply them by units; base change `k\hookrightarrow\bar k` preserves nonzero leading coefficients (actual degrees), the constant Jacobian, and both polynomial boundaries. `3|H` is base-change stable: for `\rho | \pi` with `\pi` a `k`-irreducible (separable, hence squarefree over `\bar k`), `v_\rho(a_6)=v_\pi(a_6)`, so the exponent system `v(a_6)=2t`, `v(b_9)=3t` gives `t_\rho=t_\pi` and `h_{\bar k}=h_k` up to a constant — same degree `H`. Verified independently; the composition states it compactly and correctly.

*Depression typing.* All three source documents (first gate, cube-mismatch gate, composition) state that `z=sy+r` is an identity over the coefficient extension (`L[y]`, resp. `k(x)[y]`) and not a polynomial source automorphism; the chain rule `J_{(x,y)}=s(f_xg_z-f_zg_x)` was re-derived (the `z_x` terms cancel in the determinant), and no step anywhere in the chain treats the depression as a source operation. The replay records `polynomial_source_depression=false`. No coefficient-field/source-automorphism conflation exists.

---

## Claim 2 — exhaustive field dichotomy

**CONFIRMED.**

*Exhaustive and disjoint.* `N` (`h` not a cube in `k(x)`) and `C` (`h` a cube in `k(x)`) are a statement and its negation. Well-posedness under the `k^*`-ambiguity of `h`: replacing `h` by `ch`, `c\in k^*`, does not change cube-ness because `k` is algebraically closed, so `k^*\subset (k(x)^*)^3`. This is the exact point where algebraic closedness makes the dichotomy a property of the pair rather than of a normalization choice.

*Cube side.* Independently reconstructed: if `h=f^3` with `f\in k(x)`, then `3v_\pi(f)=v_\pi(h)\ge 0` at every irreducible `\pi`, so `v_\pi(f)\ge 0` for all `\pi` and `f\in k[x]` — a rational cube of a polynomial is already a polynomial cube, with **no** constant left over. The constant `c` appears only if one insists on a monic or primitive normal form (`h=c\cdot s_0^3` with `s_0` monic): then `s=c^{1/3}s_0` needs `c^{1/3}\in k`, which `k=\bar k` supplies. Both readings give `h=s^3`, `s\in k[x]`, matching the first gate’s “Gauss’s lemma … constant times a polynomial cube, so `s` may be taken in `k[x]`”. On the noncube side, over a characteristic-zero field containing `\mu_3` (true for `\bar k(x)`… precisely: `\omega\in k\subset k(x)`), `T^3-h` is irreducible iff `h\notin k(x)^3`, so “noncube” is exactly “nontrivial cubic Kummer”, the hypothesis of the aligned branch. No intermediate (“reducible-Kummer”) case exists.

*Edge cases.* `h\neq 0` always (`a_6\neq 0` is the actual leading coefficient). `h\in k^*` (`H=0`, and `3|0`) is a cube over `\bar k`, lands in the cube branch with `s\in k^*`, which the trajectory closure’s constant-`s` case covers; in particular the constant-core `(6,9)` pairs are inside residue (A) and are excluded, not skipped. Conversely, noncube `h` is automatically nonconstant, so `H\ge 1` and `3|H` gives `H\ge 3` there.

---

## Claim 3 — noncube handoff

**CONFIRMED.**

*Derivation of `delta=0`, no circularity.* The Kummer generator is `sigma(s)=omega s`. The source coefficients `a_5,b_8\in k[x]` are `sigma`-fixed, so `A=a_5/s^5` and `B=b_8/s^8` transform by `omega^{-5}=omega` and `omega^{-8}=omega`: both weight one, hence `sigma(delta)=omega\,delta`. Independently, `delta\in k` (from the `y^{13}` row, Claim 1) is `sigma`-fixed. So `(omega-1)delta=0`; and `(omega-1)^{-1}=-(omega+2)/3` exactly modulo `omega^2+omega+1` (hand-checked product `=1`), with no division by any possibly-vanishing quantity. Hence `delta=0` is *derived* from constancy plus weight one — the composition’s (3.1) chain is exact.

*Exactly and only `c_7,c_5,c_4,c_2,c_1`.* The eight high-row integration constants `c_j` carry weight `-j \bmod 3` (re-derived from `sigma(b_j)=omega^{-j}b_j` and the weight-homogeneous potentials): nonzero weight exactly for `j\in\{7,5,4,2,1\}` (weights `2,1,2,1,2`), zero weight exactly for `j\in\{6,3,0\}`. A `k`-constant of nonzero weight vanishes; so the weight argument forces exactly (1.10) and nothing more. `c_6` is removed by the target shear `g\mapsto g-c_6f` (i.e. `Q\mapsto Q-c_6P`), `c_0` by the second-target translation; `c_3=kappa` is, per the reviewed erratum, a coordinate of the first-target-constant pin, removable by `P\mapsto P+2kappa/3` — I re-verified `g_0(a_0+q)=g_0(a_0)+(3q/2)K` exactly (because `g_0=[f^{3/2}]_+` and `[f^{-1/2}]_+=0`, the binomial expansion in `q` terminates), and the invariances `C=kappa^2+mu`, `kappa+3d/2`. The composition’s phrase “`c_3` handled covariantly” is the correct post-erratum language: the lower-Pfaffian exclusion treats every value of `kappa`, and its decisive quantities (`C`, the curve `Y^2=3X^3+4096C`, the terminal one-form, the zero-bracket coefficient) are translation-invariant.

*Byte-level input match.* The aligned lower-Pfaffian theorem’s hypotheses are: `L=k(x)(s)` nontrivial cubic Kummer, `3|deg(h)`, the depressed pair `f=z^6+a_4z^4+\dots+a_0`, `g=g_0(a)+kappa K` (i.e. `z^5` and `z^8` absent — the latter is `delta=0`, supplied by this branch), the four lower zero rows, and terminal `[z^0]D=j/s`. Every one of these is emitted by the landing plus this handoff, and the boundaries remain charged though the exclusion **uses no boundary at all** (“the result uses no boundary reduction”), so “still present” in the composition is accurate and harmless. The exclusion itself was spot-re-derived at its load-bearing points: weights `(a_0,\dots,a_4,kappa)=(0,2,1,0,2,0)` and `wt(I_4,I_3,I_2,I_1)=(1,2,0,1)` (checked monomial by monomial against the displayed `e_4,e_3,N_2,N_1`), forcing `I_4=I_3=I_1=0`, `I_2=mu\in k`; the prime-kernel no-switching argument; sheet `P_A` zero-bracket (`D=0` identically for `f=K^2+d`, `g=K^3+(kappa+3d/2)K`); sheet `P_B`’s `C\neq0` forbidden-value valuation `ord_p(h)=3-6e<0`; the `C=0` factorization `EB=(3/4)X^2(X-3a_4^2)` — expanded by hand and equal to `384a_2^3-432a_2^2a_4^2+144a_2a_4^4-15a_4^6`; and the shifted-DS terminal `189h^4q^6(2h'q+3hq')=j`, whose infinity count I re-derived independently via `w=h^2q^3`, `Phi=h^3q^4\,w'`: `deg(Phi)=r-1` with leading coefficient containing `-\sum k_i\neq0`, so constancy forces `r=1`, then `e=3+7k`, `3|H\Rightarrow 3|k\Rightarrow h=(C^{1/3}(x-a)^{1+7\ell})^3` is a cube — contradicting noncube. The `3|H` hypothesis is consumed exactly here and is in the replay’s consume set.

*No illicit imports.* The exclusion neither invokes nor repairs the first gate’s full-cubic boundary `TYPE-FAIL` (it uses no boundary), makes no orbit-degree-three assumption, and never treats `z=sy+r` as a source map. The replay’s forbidden-import flags match the documents.

---

## Claim 4 — cube handoff and second partition

**CONFIRMED.**

*No Kummer import.* When `h=s^3` with `s\in k[x]`, `L=k(x)` and there is no Galois action; the cube-mismatch gate states, and the trajectory gate repeats, that none of `c_7,c_5,c_4,c_2,c_1` may be weight-discarded, and neither document does so. The `X=sR` descent of the noncube branch is likewise not imported — on the cube side `X,Y\in k(x)` directly, and the elliptic-sheet exclusion there is by genus (Riemann–Hurwitz constancy of `P^1\to E`), a different and correctly chosen argument. The replay aborts if the vanishing fact enters the cube route.

*Faber landing.* `g=[H(f^{1/6})]_+` with `H(T)=T^9+dT^8+c_7T^7+\dots+c_0` — nine constants before quotient — is the complete high-row solution (triangular uniqueness, one constant per row, re-checked structurally; `d=b_8=-delta/2` is the constant `z^8` coefficient from Claim 1). The first-target translation action (3.2) was re-derived by expanding `(w^6+q)^{1/6}=w+(q/6)w^{-5}+O(w^{-11})` through `H`: coefficients shift by exactly `-3q/2` on `T^3`, `-4dq/3` on `T^2`, `-7c_7q/6` on `T`, `-c_6q` on `1`, others fixed. Hence the `d\neq0` invariants `mu=8dc_3-9c_2`, `nu=8dc_1-7c_7c_2` (checked), and the division-free `d=0` quotient `c_3=0` retaining `c_7,c_5,c_4,c_2` and `\bar c_1=nu_0/9`, `nu_0=9c_1-7c_7c_3` (checked; valid at `c_7=0`).

*Lower rows.* `J_{(x,z)}=f_z\sum_{n\ge1}r_n'w^{-n}` was re-derived at fixed `w`; `[f_zw^{-n}]_+=0` for `n\ge6`; the `A_n` of (4.3) were re-derived including the constant `a_2-a_4^2/12` of `A_1`; the matrix to rows `z^4..z^0` is triangular with determinant `6^5`, so the remaining Keller equation is *equivalent to* `r_1'=r_2'=r_3'=r_4'=0`, `6r_5'=j/s` — an equivalence, not a projection.

*Finite-pole theorem.* Re-derived in full: a simple root of `s` gives `j/(6s)` a simple pole, impossible for a rational derivative; a multiplicity-`e_i\ge2` root gives `r_5` pole order `e_i-1`; no other finite pole; pole degree `m-r`; at infinity `r_5-c \sim jx^{1-m}/(6\,lc(s)(1-m))` (zero of exact order `m-1`, no residue at infinity since a rational derivative has none anywhere); zero degree = pole degree forces `m-1\le m-r`, so `r=1`, and `m=1` is the logarithm case. Exactly `s\in k^*` or `s=C(x-a)^m`, `m\ge2`, independent of `d` — so the composition is right that the split `d=-delta/2` happens **after** the full landing.

*Trajectory closure, both branches, all strata.* The weight system `wt(a_i)=6-i`, `wt(d,c_7,c_5,c_4,c_3,c_2,c_1)=(1,2,4,5,6,7,8)`, `wt(r_n)=9+n` (re-derived from `H(T)` weight 9) makes the first-nonzero-load ordering collision-free: `d` (weight 1) strictly first when nonzero; then `c`’s at distinct `2,4,5,7,8`; then targets `rho_1..rho_4` at `10,11,12,13`; terminal-only at `14` (unit ideal). Independent checks: the `d\neq0` orbit equation `2q^2-90q+135=0` gives `q=(45\pm3\sqrt{195})/2` (hand-solved; `4q+27=0` would force `780=1521`), both squarefree, excluded at constant `s` by `deg(a_4)=2/13\notin Z` and at monomial `s` by the boundary order split `\le1` vs exactly `3/2` against the requirements `12/k`, `18/k` (re-derived from `P_0=L^6\bar F(t,R)`, `Q_0=L^9\bar G(t,R)`); every `d=0` high-constant support fails integrality — checked case by case: `k=2`: `2p=1/6`, `3p=1/4`; `k=4`: `2p=1/5`; `k=5`: `3p=1/3` or `2p=2/9`; `k=7`: `2p=2/7`; `k=8`: `3p=1/2` or `2p=1/3` — and monomial cores fail the strict boundary inequalities for all `k\le8`; `rho_1` fails at `p=1/4`, `rho_2` at the fractional normal corrections `(-1/2,-1/6,1/6)`; DS-leading cores fail at `p=1/14` (constant `s`) or by the nonzero DS resultant `3^97^2/2^5` (monomial); double-root arcs die on the load-independent `r_3=-1/16` at `h^3` (and `r_4=-3/16` after `S=0`); the triple point is not projective.

*Mixed `rho_3,rho_4`.* Exactly as the composition states: `rho_1=rho_2=0` is forced first; `mu=6rho_3`, `nu=6rho_4`; the split is `nu\neq0` vs `nu=0`, and `rho_4` is never set to zero on a nonzero-`rho_3` row. Re-derived: `(7.4)` solves `q=4w/A+8B^2/A^2`, `p=-8Bw/A^2-32B^3/A^3` from `e_4=e_3=0` (checked by substitution); `A=0` forces `B=0` then `nu=0`, so localization at `A` loses nothing when `nu\neq0`; for `mu\neq0` the curve `72V^2=3A^3+512mu` is smooth genus one, so a rational path is constant and `6r_5'=j/s` fails; for `mu=0` the cusp normalization `A=24lambda^2`, `V=24lambda^3` (checked: `72\cdot576=3\cdot13824`) gives `r_5=(27/2)lambda^7-nu^2/(1458lambda^6)` (checked: `13824/1024=27/2`, `373248/256=1458`), a function with two distinct poles (order 6 at `lambda=0`, order 7 at `lambda=\infty`), while both terminal forms (`alpha x+beta`; `c+jt^{1-m}/(6C(1-m))`) have exactly one pole point — contradiction, covering `rho_3=0,rho_4\neq0` too. For `nu=0`, the `kappa=0` specialization of the reviewed universal two-sheet decomposition applies as pure algebra: zero-bracket sheet has `D=0`; elliptic sheet is genus one for `mu\neq0`; `mu=0` is zero-bracket or the DS curve `r_5=(27/2)lambda^7`, killed by the seventh-power valuation (`7\nmid1` at a simple zero; `c=0` and `m=7\ell+1` forced at a monomial core) plus the DS resultant against both original boundaries.

*Targeted search for an omitted case.* (i) A “third `h` type”: impossible, cube/noncube is excluded middle, and `T^3-h` has no intermediate factorization over a field containing `\mu_3`. (ii) Reducible Kummer: same point — reducible iff cube, and then the branch is the cube branch. (iii) Repeated roots: `h` with arbitrary multiplicities is handled by the valuation arguments as written (no squarefreeness assumed); repeated-root `s` is the monomial branch `m\ge2`; the double-root cubic `K` stratum is closed by `(3.3)`. (iv) Constant `s`: present in every stratum of the trajectory gate and in the finite-pole theorem. No omission found.

---

## Claim 5 — adversarial typing controls

**CONFIRMED**, with the honest boundary stated below.

*Noncube control, independently evaluated.* `h=x(x-1)(x-2)=x^3-3x^2+2x`; the divisor valuation at `x=0` is `v_0(h)=1` (also `h(0)=0`, `h'(0)=2`, so the zero is simple). A cube in `k(x)` has every valuation divisible by three; `1\notin 3Z`, so `h` is not a cube — derived, not asserted. In the replay, `delta` is *not* initialized to zero: the fact `delta_zero_derived` is emitted only after the exact `(omega-1)`-inverse identity is verified in `Q[omega]/(omega^2+omega+1)` and the fixed/weight-one relation is consumed; I re-derived that inverse by hand. The route then, and only then, consumes the aligned exclusion.

*Cube `d=0` control, independently evaluated.* `(x^2+1)^3=x^6+3x^4+3x^2+1` (hand-multiplied), `H=6`, `3|6`. The route emits `d_zero` with `c_7=1` retained; the retained-constant tuple is pinned to `(c_7,c_5,c_4,c_2,c_1)` and `c_7=1` is re-checked after the Faber landing consume; the route hard-aborts if `c7_c5_c4_c2_c1_weight_forced_zero` ever appears among its facts, i.e. if aligned Kummer vanishing leaked into the cube quotient. The routing is to the separate `d=0` five-constant quotient, matching cube-mismatch (3.4) and trajectory (1.2).

*Can a control pass while the real branch typing is wrong?* **Yes, in principle — and the composition says so itself.** The controls exercise (a) two small pieces of genuine algebra (a valuation, a cyclotomic inverse, a cube expansion) and (b) the replay’s fact-flow DAG. They cannot detect an error *inside* the reviewed leaf theorems (for instance, a hidden boundary reduction in the lower-Pfaffian gate, or a lost stratum in the trajectory gate) because the replay consumes those theorems as named facts. The report’s own scoping — “a routing control, not a claim that the displayed constants themselves solve the Faber equations”; “PASS strings are regression markers only; the reviewed reports are the mathematical evidence” — is therefore exactly right, and this review’s verdicts on Claims 3 and 4 rest on the leaf documents and independent derivations, not on the controls. Within their stated scope, both controls are correct, and they do pin the two historically dangerous failure modes (initializing `delta=0` instead of deriving it; importing weight vanishing into the cube core).

---

## Claim 6 — degree recursion

**CONFIRMED.**

*Route side conditions, independently verified.* `Z` (`m=0`): `det J = P_xQ_y=j` forces `P=cx+e`, `Q=(j/c)y+g(x)` — automorphic with `n=1`; classes `(0,0)` and `(0,n)`, `n\ge2`, are empty. `G` (`gcd(m,n)=d\le2`): the shear lemma’s exact degrees `deg\,sigma_L(P)=a(H+dL)`, `deg\,sigma_L(Q)=b(H+dL)`, `gcd=H+dL` were re-derived (single dominating monomial `lc_x(a_m)x^{aH+Lm}`, no cancellation for `L>max(M,1)`); with `g=gcd(H,d)\in\{1,2\}` Dirichlet gives `H_0+d_0L` prime, so the transformed total gcd is `p` (Nagata 7.3, the repaired Appelgate–Onishi) or `2p` (GGV 2017), for **every** `H`, including `H=0` via prime `L`. `D` (`m|n`, `m<n`): `a_m=alpha h`, `b_n=beta h^{n/m}` gives `b_n=(beta/alpha^{n/m})a_m^{n/m}`, so `Q\mapsto Q-cP^{n/m}` is an elementary target automorphism strictly lowering the larger degree. `E` (`m=n\ge1`): `(1.1)` gives constant leading ratio; one `GL_2` step lowers one coordinate. Children are enumerated conservatively over **all** `r<n`, so the unknown actual result degree cannot escape. Measure `(max(m,n),m+n)`: `D` children have `max\le n-1` (first coordinate strictly drops); `E` children keep `max=n` and drop the sum by at least one — strict lexicographic decrease on every edge, so the recursion terminates; I asserted this per-edge in the generator below rather than assuming it.

*Independent unordered table, `0<=m<=n<=11`* (priority `Z`, then `G`, then `E`, then `D`, then `X`; identical closure to the producer’s convention, which is noted to differ only in labeling `(1,1),(2,2)`):

| `n` | `Z` | `G` | `D` | `E` | `X` |
|---:|---|---|---|---|---|
| 0 | `0` | — | — | — | — |
| 1 | `0` | `1` | — | — | — |
| 2 | `0` | `1,2` | — | — | — |
| 3 | `0` | `1,2` | — | `3` | — |
| 4 | `0` | `1,2,3` | — | `4` | — |
| 5 | `0` | `1,2,3,4` | — | `5` | — |
| 6 | `0` | `1,2,4,5` | `3` | `6` | — |
| 7 | `0` | `1,2,3,4,5,6` | — | `7` | — |
| 8 | `0` | `1,2,3,5,6,7` | `4` | `8` | — |
| 9 | `0` | `1,2,4,5,7,8` | `3` | `9` | `6` |
| 10 | `0` | `1,2,3,4,6,7,8,9` | `5` | `10` | — |
| 11 | `0` | `1,2,3,4,5,6,7,8,9,10` | — | `11` | — |

Row-by-row equal to the composition’s table. Count `\sum_{n=0}^{11}(n+1)=78` unordered; swap symmetry gives `144` ordered.

*Complete `D/E` child audit* (every child listed, every child closes):

```text
D(3,6):  (0,3)Z (1,3)G (2,3)G (3,3)E (3,4)G (3,5)G
D(4,8):  (0,4)Z (1,4)G (2,4)G (3,4)G (4,4)E (4,5)G (4,6)G (4,7)G
D(3,9):  (0,3)Z (1,3)G (2,3)G (3,3)E (3,4)G (3,5)G (3,6)D (3,7)G (3,8)G
D(5,10): (0,5)Z (1,5)G (2,5)G (3,5)G (4,5)G (5,5)E (5,6)G (5,7)G (5,8)G (5,9)G
E(n,n):  children (r,n), r<n, are exactly the row-n entries above; in particular
E(9,9):  includes (6,9) -> X   (the only recursion edge into the primitive)
E(10,10),E(11,11): all children G/Z/D per rows 10,11
```

The only non-`Z/G/D/E` pair with `max<=11` is `(6,9)` (systematic check: pairs with `gcd\ge3` and `n\le11` are `3\cdot(1,2),3\cdot(1,3),4\cdot(1,2),5\cdot(1,2)` — all `D` — and `3\cdot(2,3)=(6,9)`). Pre-composition the unique open terminal, reached directly and through `(9,9)`, is `(6,9)` with `3|H`; `3\nmid H` closes by the prime shear (`gcd(H,3)=1` Dirichlet). Post-composition nothing is open. Frontier at `n=12` (checksum only): `m=0`:Z; `1,2,5,7,10,11`:G; `3,4,6`:D; `12`:E; `8`:`gcd 4, 12\bmod8=4` OPEN; `9`:`gcd 3, 12\bmod9=3` OPEN — exactly `(8,12),(9,12)`. Note `(6,12)` is *not* a new primitive: its `D` children include `(6,9)`, closed by this composition.

*Reproducible generator.* The following script (written by this reviewer from scratch; not derived from `replay.py`) reproduces the table, the child audit with per-edge measure assertions, the 78/144 counts, the unique pre-composition terminal, and the frontier. It was written to `/tmp/gcd3_69_review_claude/degree_audit_claude.py`; because this review environment has no interpreter, its output above is the hand-traced evaluation, and rerunning it is part of the operator regression.

```python
from math import gcd
def route(m, n):
    if m > n: m, n = n, m
    if m == 0: return "Z"
    if gcd(m, n) <= 2: return "G"
    if m == n: return "E"
    if n % m == 0: return "D"
    if (m, n) == (6, 9): return "X"
    return "OPEN"
def children(m, n):
    r_ = route(m, n)
    if r_ == "E": return [tuple(sorted((r, n))) for r in range(n)]
    if r_ == "D": return [tuple(sorted((m, r))) for r in range(n)]
    return []
def measure(p): return (max(p), p[0] + p[1])
def close(pair, x69_closed):
    m, n = sorted(pair); r_ = route(m, n)
    if r_ in ("Z", "G"): return True, set()
    if r_ == "X": return ((True, set()) if x69_closed else (False, {(m, n)}))
    if r_ == "OPEN": return False, {(m, n)}
    ok, opens = True, set()
    for c in children(m, n):
        assert measure(c) < measure((m, n))
        k, o = close(c, x69_closed); ok = ok and k; opens |= o
    return ok, opens
# table rows, 78/144 counts, pre/post-composition open terminals, and
# frontier = [(m,12) for m in range(13) if route(m,12)=="OPEN"] == [(8,12),(9,12)]
```

---

## Claim 7 — field theorem and descent

**CONFIRMED.**

*Emptiness (A) descends trivially.* A `(6,9),3|H` Keller pair over `k` base-changes to one over `\bar k` with the same actual degrees (leading coefficients stay nonzero), the same constant Jacobian, the same polynomial boundaries, and the same `H` (Claim 1’s separability computation `t_\rho=t_\pi`). Emptiness over `\bar k` therefore forbids the pair over `k`.

*Automorphy (B) descends.* Two independent routes, both valid: (i) a polynomial inverse is unique, so for the (infinite, normal, separable in characteristic zero) extension `\bar k/k`, every element of `Gal(\bar k/k)` fixes the inverse of `(P,Q)` coefficientwise, and the fixed field is `k`; (ii) `M=k[x,y]/k[P,Q]` satisfies `M\otimes_k\bar k=0`, and `\bar k` is faithfully flat over `k`, so `M=0`. The cited total-degree theorems (Nagata over the 1989 symposium scope, GGV over an arbitrary characteristic-zero field) are consumed after embedding the finitely generated coefficient subfield’s closure into `C` where needed — the as109 review verified this chain against the primary sources.

*Attacks.* Inseparability: vacuous in characteristic zero. Nonclosed constants: all branch work happens after base change; nothing downstream re-imports a `k`-rationality assumption (the noncube branch needs `omega\in k` and cube roots of constants — supplied by `\bar k`; descent happens only at the two displayed points). Leading-coefficient cancellation: no operation in the chain (swap, scaling, shear, `GL_2`, base change) can kill `a_6` or `b_9`; the `D/E` shears intentionally kill only the *other* coordinate’s leading term, and the resulting unknown degree is child-enumerated exhaustively. Target swap: negates `j`, permutes degrees; all cited theorems are swap-stable; the `m<=n` normalization is pure bookkeeping.

---

## Claim 8 — logical boundary

**CONFIRMED.**

The strongest theorem actually supported is exactly the displayed pair (A)+(B), over an arbitrary characteristic-zero field, in actual partial `y`-degrees, plus the maximum-twelve **checksum**. Every leaf dependency is (a) exact, (b) hostile-reviewed CONFIRMED in frozen bytes, and (c) consumed at or below its reviewed scope; no leaf is computationally sampled (the two Singular decompositions are certified universal computations, re-run by the leaf reviewer on a second engine and monomial order), none remains provisional after the trajectory review landed, and no hypothesis mismatch was found at any handoff (Claims 1–4). In particular:

- **Arbitrary support:** not supported and not claimed; pairs with `deg_y>11` outside `(6,9),3|H` are untouched.
- **Total degree at most eleven:** the implication `max total degree <=11 \Rightarrow max deg_y <=11 \Rightarrow` automorphism *does* follow a fortiori from (B), but it is strictly weaker than (B), classically known (total-degree results well beyond eleven exist in the cited literature), and not part of the composition’s claim. It must not be advertised as an output or novelty of this work; the promotion language stays (A)+(B).
- **Maximum twelve:** `(8,12)` and `(9,12)` are open primitives; `(12,12)` is derivative on them through `E`; no theorem exists or is claimed.
- **Polynomial counterexample:** nothing here constructs one; every exhibited family (e.g. `(K^2,K^3)`, the Artinian jets, the local formal survivor) has zero or non-constant Jacobian or is non-rational, and each source document says so.
- **JC2:** requires unbounded degrees; explicitly not claimed anywhere in the chain, and the replay records `JC2: NOT_CLAIMED`.

The smallest exact missing obligations are the two process items in the header (operator regression rerun; committing the hash-pinned uncommitted bytes). Neither is a mathematical gap, and averaging them into the mathematical verdict would be wrong in both directions.

---

## Non-blocking remarks

1. **Symbol overloading across documents.** `d` is the cube-branch mismatch `-delta/2` in the composition and cube gates, but also the `P_A`-sheet deformation `w/4` in the lower-Pfaffian gate; `mu,nu` denote `I_2`-type invariants, `d\neq0` target invariants (`8dc_3-9c_2`, `8dc_1-7c_7c_2`), and `6rho_3,6rho_4` in different documents. Each use is internally consistent and the composition itself uses only `d=-delta/2`; a future synthesis document should rename.
2. **“Committed basis” precision.** Eleven ledger files are committed at `1e60fce…`; the trajectory review (and the composition artifacts) are hash-pinned working-tree files. The fail-closed replay makes this safe, but the next bank commit should include them.
3. **`(1,1),(2,2)` labels.** Producer table says `G`, as109 said `E`; both routes close them; the composition discloses the convention.
4. **Boundary jets in the noncube branch.** The composition consume-set requires `original_Taylor_boundaries_retained` for the aligned exclusion even though that theorem uses no boundary. Requiring an unused premise is fail-closed and harmless; noted for exactness.
5. **Controls are necessary-not-sufficient** (Claim 5). This is already the report’s own position; recorded here so no future reader upgrades a replay PASS into mathematical evidence.

---

## Promotion (restated)

Accept: **(A)** the `(6,9),3|H` residue of characteristic-zero Keller pairs is empty; **(B)** every characteristic-zero Keller pair with maximum actual `y`-degree at most eleven is a polynomial automorphism; the maximum-twelve frontier checksum is exactly `(8,12),(9,12)`. Next work: operator regression rerun and bank commit; then the `(8,12)`/`(9,12)` landings. No generic coefficient search, no AWS.

## Quarantine (end)

Do not promote to arbitrary support, a new total-degree theorem, maximum twelve, a polynomial counterexample, polynomial source depression, cube-core Kummer vanishing, full-cubic boundary reduction, or JC2. PASS strings — including the composition’s own — are regression markers only. The byte-attestation layer of this review is quarantined as not executed in this environment: the two registered commands remain to be run by the operator, and this review’s hash table is a cross-document consistency check, not a recomputation. The mathematical verdicts above rest on full readings of the twelve reviewed source documents and on the independent derivations displayed, and on nothing else. No result in this review proves or disproves JC2.
