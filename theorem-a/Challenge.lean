/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), Claude / Anthropic agents (drafting)
-/
import Mathlib

/-!
# Challenge: rigidity of the weighted derivation identity (Theorem A)

Statement module (Palomar registry).  The result:

**Theorem A** (ODE rigidity, all weights).  Let `F` be an integral domain of
characteristic zero, `ν ≥ 1` an integer, and let `A, C ∈ F[y]` satisfy

  `A·C′ − ν·A′·C = c`  for some constant `c ∈ F`, `c ≠ 0`.

Then `deg A ≤ 1`.

This is the theorem labelled `thm:ode` — “ODE rigidity, all weights”,
Theorem 6.1 in the current compilation — in Section 6 of the campaign paper;
it is stated and proved as Theorem A in `MATHIEU.md` §5.1 of the archived
campaign theory bundle (Zenodo, DOI 10.5281/zenodo.22002825).  There it
closes the depth-two block of the strip reduction of the plane Jacobian
problem at Newton-degree pair `(72,108)`: through the block-to-ODE bridge it
forces the edge polynomial `A` of a hypothetical Keller counterexample to be
binomial.  (The log-residue block-variety theorem `thm:R` of the same
section is *not* formalized here.)  Dividing the identity by `A^{ν+1}` gives
`(C/A^ν)′ = c/A^{ν+1}`, so the statement is a non-rationality lemma for
`∫ dy/A^{ν+1}`.  Prior art: Lemma A.7 in the appendix of Żołądek, *An
application of Newton–Puiseux charts to the Jacobian problem*, Topology 47
(2008) 431–469, yields the case where `A` has at least two distinct roots
(perfect-power `A` needs a separate evaluation argument); and for `ν = 1`,
Theorem 4 of Hermoso–Alcázar, arXiv:2410.18867, forces both polynomials of a
nonzero-constant-Wronskian pair to be affine.  The proof formalized here is
the campaign's independent one, staying inside `F[y]`.  The source states
the theorem over a field; an integral domain suffices and is what is
formalized.

`TheoremA_charP` is a standalone strengthening extracted from the Section 6
proof and its closing positive-characteristic remark (`MATHIEU.md` §5.4):
the same rigidity holds over a domain of characteristic `p` once `p`
dominates the degree data, `ν·deg A < p` and `deg C < p`.  The source
records only the conservative block-level bound `p > (k+1)·d₂` (application:
`ν = k`, `deg A ≤ d₂`, `deg C ≤ k·d₂`), which implies both hypotheses; the
standalone statement is not displayed there.  Some bound is necessary: in
characteristic `p` the pair `A = y^p + y`, `C = 1`, `ν = 1` has
`A·C′ − A′·C = −1` and `deg A = p ≥ 2`.

Reading conventions (all standard Mathlib):
* `Polynomial.derivative` is the formal derivative on `F[y]`.
* `Polynomial.natDegree` is the degree as a natural number, with
  `natDegree 0 = 0` — harmless here, since the hypotheses force `A ≠ 0`.
* `Polynomial.C : F →+* F[y]` embeds constants, so `Polynomial.C c` is the
  constant polynomial `c`, and `(ν : Polynomial F)` is the natural number `ν`
  cast into `F[y]`.
* `CharP F p` says `F` has characteristic `p`; an integral domain has
  characteristic zero or a prime.
-/

/-- **Theorem A** (ODE rigidity, all weights; characteristic zero).
If polynomials `A, C` over an integral domain `F` of characteristic zero
satisfy `A·C′ − ν·A′·C = c` with integer weight `ν ≥ 1` and `c` a nonzero
constant, then `deg A ≤ 1`.  (Theorem `thm:ode`, “ODE rigidity, all
weights”, Section 6 of the campaign paper — Theorem 6.1 in the current
compilation; Theorem A in `MATHIEU.md` §5.1 of the archived bundle,
DOI 10.5281/zenodo.22002825.) -/
theorem TheoremA {F : Type*} [CommRing F] [IsDomain F] [CharZero F]
    (ν : ℕ) (hν : 1 ≤ ν) (A C : Polynomial F) (c : F) (hc : c ≠ 0)
    (hode : A * Polynomial.derivative C
        - (ν : Polynomial F) * (Polynomial.derivative A * C) = Polynomial.C c) :
    A.natDegree ≤ 1 := by
  sorry

/-- **Theorem A, positive characteristic.**  Over an integral domain of
characteristic `p`, the same rigidity holds provided `p` dominates the degree
data: `ν·deg A < p` and `deg C < p`.  (A standalone strengthening extracted
from the Section 6 proof and the closing positive-characteristic remark of
the campaign paper, cf. `MATHIEU.md` §5.4: in the application there `ν = k`,
`deg A ≤ d₂`, `deg C ≤ k·d₂`, so the recorded conservative bound
`p > (k+1)·d₂` implies both hypotheses.) -/
theorem TheoremA_charP {F : Type*} [CommRing F] [IsDomain F] (p : ℕ) [CharP F p]
    (ν : ℕ) (hν : 1 ≤ ν) (A C : Polynomial F) (c : F) (hc : c ≠ 0)
    (hνA : ν * A.natDegree < p) (hC : C.natDegree < p)
    (hode : A * Polynomial.derivative C
        - (ν : Polynomial F) * (Polynomial.derivative A * C) = Polynomial.C c) :
    A.natDegree ≤ 1 := by
  sorry
