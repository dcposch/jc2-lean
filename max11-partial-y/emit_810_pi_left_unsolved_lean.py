#!/usr/bin/env python3
"""Emit the block-split, unsolved left factorization of the 810 pi numerator.

The source of truth is the nineteen generic-ring blocks in
`Sol810PiSourceClearingDraftScratch.lean`.  Only the six valuation
substitutions are made; none of the four scalar load solves is inserted.
For every source block the script verifies divisibility by `h^96` and emits
an exact `head + h * tail` quotient together with a small Lean ring proof.
"""

from argparse import ArgumentParser
from pathlib import Path
import re

import sympy as sp


ROOT = Path(__file__).parent
SOURCE = ROOT / "Sol810PiSourceClearingDraftScratch.lean"
BLOCK_PREFIX = "localClearedSixteenthDefectBlock"
BLOCK_COUNT = 19

h, t0, v1, u1, a4, a3, a2, a1, a0 = sp.symbols(
    "h t0 v1 u1 a4 a3 a2 a1 a0"
)
s1, w1, b62, b5, b4, b3, b2, b1, lam = sp.symbols(
    "s1 w1 b62 b5 b4 b3 b2 b1 lam"
)
a7, a6, a5, b8, b7, b6 = sp.symbols("a7 a6 a5 b8 b7 b6")

SOURCE_ARGUMENTS = (
    h, a7, a6, a5, a4, a3, a2, a1, a0,
    b8, b7, b6, b5, b4, b3, b2, b1, lam,
)
QUOTIENT_ARGUMENTS = (
    h, t0, v1, u1, a4, a3, a2, a1, a0,
    s1, w1, b62, b5, b4, b3, b2, b1, lam,
)
HEAD_ARGUMENTS = QUOTIENT_ARGUMENTS[1:]
SYMBOLS = {symbol.name: symbol for symbol in SOURCE_ARGUMENTS + QUOTIENT_ARGUMENTS}
SYMBOLS["lambda"] = lam

SUBSTITUTION = {
    a7: h**6 * t0,
    a6: h**4 * v1,
    a5: h**2 * u1,
    b8: h**6 * s1,
    b7: h**4 * w1,
    b6: h**2 * b62,
}


def definition_body(name: str) -> str:
    text = SOURCE.read_text()
    start = text.index(f"def {name}")
    body_start = text.index(":=", start) + 2
    match = re.search(r"\n(?:def |end |section |/-!|set_option|/--)", text[body_start:])
    if match is None:
        raise RuntimeError(f"could not find end of {name}")
    return text[body_start : body_start + match.start()]


def parse_block(index: int) -> sp.Expr:
    pattern = re.compile(r"^\s*([+-]?)\s*\(([0-9]+) : R\)(.*)$")
    terms = []
    for raw_line in definition_body(f"{BLOCK_PREFIX}{index}_810").splitlines():
        line = raw_line.rstrip()
        if not line:
            continue
        match = pattern.match(line)
        if match is None:
            raise RuntimeError(f"unparsed block {index} line: {line}")
        sign, coefficient, factors = match.groups()
        scalar = int(coefficient) * (-1 if sign == "-" else 1)
        factors = re.sub(r"\blambda\b", "lam", factors.replace(" ^ ", "**"))
        terms.append(sp.sympify(f"{scalar}{factors}", locals=SYMBOLS))
    return sp.Add(*terms)


def block_parts(index: int) -> tuple[sp.Expr, sp.Expr]:
    specialized = sp.Poly(sp.expand(parse_block(index).subs(SUBSTITUTION)), h)
    exponents = [monomial[0] for monomial, _ in specialized.terms()]
    if min(exponents) < 96:
        raise RuntimeError(f"block {index} has exponent below 96: {min(exponents)}")
    head = sp.expand(specialized.coeff_monomial(h**96))
    tail = sp.expand(
        sum(
            specialized.coeff_monomial(h**exponent) * h ** (exponent - 97)
            for exponent in sorted(set(exponents))
            if exponent >= 97
        )
    )
    if sp.expand(specialized.as_expr() - h**96 * (head + h * tail)) != 0:
        raise RuntimeError(f"block {index} factorization failed")
    return head, tail


def lean_polynomial(expression: sp.Expr, variables: tuple[sp.Symbol, ...]) -> str:
    polynomial = sp.Poly(sp.expand(expression), *variables, domain=sp.ZZ)
    if polynomial.is_zero:
        return "    0"
    lines = []
    for position, (monomial, coefficient) in enumerate(polynomial.terms()):
        negative = coefficient < 0
        absolute = abs(int(coefficient))
        factors = []
        if absolute != 1 or not any(monomial):
            factors.append(f"({absolute} : R)")
        for variable, exponent in zip(variables, monomial):
            variable_name = "lambda" if variable == lam else str(variable)
            if exponent == 1:
                factors.append(variable_name)
            elif exponent:
                factors.append(f"{variable_name} ^ {exponent}")
        term = " * ".join(factors) if factors else "(1 : R)"
        if position == 0:
            prefix = "    - " if negative else "    "
        else:
            prefix = "    - " if negative else "    + "
        lines.append(prefix + term)
    return "\n".join(lines)


def arguments(arguments: tuple[sp.Symbol, ...]) -> str:
    return " ".join("lambda" if argument == lam else str(argument) for argument in arguments)


def block_call(stem: str, index: int, include_h: bool) -> str:
    args = QUOTIENT_ARGUMENTS if include_h else HEAD_ARGUMENTS
    return f"{stem}{index}_810 {arguments(args)}"


def emit_header() -> None:
    print("import Sol810PiSourceClearingDraftScratch")
    print()
    print("/-! # Polynomial-uniform unsolved left jet for the 810 pi numerator")
    print()
    print("This file makes only the six displayed valuation substitutions.  In")
    print("particular it does not insert any scalar load solve, so its order-96")
    print("factorization remains valid when first-order deviations are retained. -/")
    print()
    print("noncomputable section")
    print()
    print("namespace Max11DegreeRoutes")
    print()
    print("set_option maxRecDepth 1000000")
    print()
    print("section PiLeftUnsolvedBlocks810")
    print()
    print("variable {R : Type*} [CommRing R]")
    print()


def emit_block(index: int) -> None:
    head, tail = block_parts(index)
    head_args = arguments(HEAD_ARGUMENTS)
    quotient_args = arguments(QUOTIENT_ARGUMENTS)
    source_specialized = (
        f"{BLOCK_PREFIX}{index}_810 h (h ^ 6 * t0) (h ^ 4 * v1) "
        f"(h ^ 2 * u1) a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1) "
        f"(h ^ 2 * b62) b5 b4 b3 b2 b1 lambda"
    )
    print(f"/-- Order-96 head contributed by source block {index}. -/")
    print(f"def piLeftUnsolvedHeadBlock{index}_810 ({head_args} : R) : R :=")
    print(lean_polynomial(head, HEAD_ARGUMENTS))
    print()
    print(f"/-- Quotient tail contributed by source block {index}. -/")
    print(f"def piLeftUnsolvedTailBlock{index}_810 ({quotient_args} : R) : R :=")
    print(lean_polynomial(tail, QUOTIENT_ARGUMENTS))
    print()
    print("set_option maxHeartbeats 100000000 in")
    print(f"private theorem piLeftUnsolvedBlock{index}_factored810")
    print(f"    ({quotient_args} : R) :")
    print(f"    {source_specialized} =")
    print(f"      h ^ 96 * ({block_call('piLeftUnsolvedHeadBlock', index, False)} +")
    print(f"        h * {block_call('piLeftUnsolvedTailBlock', index, True)}) := by")
    print(f"  simp only [{BLOCK_PREFIX}{index}_810,")
    print(f"    piLeftUnsolvedHeadBlock{index}_810, piLeftUnsolvedTailBlock{index}_810]")
    print("  ring")
    print()


def emit_sum_definition(name: str, stem: str, include_h: bool) -> None:
    args = QUOTIENT_ARGUMENTS if include_h else HEAD_ARGUMENTS
    print(f"def {name} ({arguments(args)} : R) : R :=")
    for index in range(BLOCK_COUNT):
        prefix = "    " if index == 0 else "    + "
        print(prefix + block_call(stem, index, include_h))
    print()


def emit_footer() -> None:
    quotient_args = arguments(QUOTIENT_ARGUMENTS)
    emit_sum_definition("piLeftUnsolvedHead810", "piLeftUnsolvedHeadBlock", False)
    emit_sum_definition("piLeftUnsolvedTail810", "piLeftUnsolvedTailBlock", True)
    print("set_option maxHeartbeats 400000000 in")
    print("/-- Exact polynomial-uniform order-96 factorization before any scalar")
    print("load solve is inserted. -/")
    print("theorem localClearedSixteenthDefect810_left_unsolved_factored")
    print(f"    ({quotient_args} : R) :")
    print("    localClearedSixteenthDefect810")
    print("        h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)")
    print("        a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)")
    print("        (h ^ 2 * b62) b5 b4 b3 b2 b1 lambda =")
    print("      h ^ 96 * (piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0")
    print("        s1 w1 b62 b5 b4 b3 b2 b1 lambda +")
    print("        h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0")
    print("          s1 w1 b62 b5 b4 b3 b2 b1 lambda) := by")
    print("  simp only [localClearedSixteenthDefect810,")
    print("    localClearedSixteenthDefectCore810]")
    for index in range(BLOCK_COUNT):
        print(f"  rw [piLeftUnsolvedBlock{index}_factored810]")
    print("  simp only [piLeftUnsolvedHead810, piLeftUnsolvedTail810]")
    print("  ring")
    print()
    print("end PiLeftUnsolvedBlocks810")
    print()
    print("section PiLeftUnsolvedRootPeel810")
    print()
    print("variable {k : Type*} [Field k] [CharZero k]")
    print()
    print("/-- A weight-112 source power relation kills the unsolved order-96 head")
    print("at every root of the local parameter. -/")
    print("theorem piLeftUnsolvedHead810_eval_root_of_power")
    print("    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])")
    print("    (lambda eta x : k) (hh : h ≠ 0) (hroot : h.eval x = 0)")
    print("    (hpower :")
    print("      localClearedSixteenthDefect810")
    print("          h (h ^ 6 * t0) (h ^ 4 * v1) (h ^ 2 * u1)")
    print("          a4 a3 a2 a1 a0 (h ^ 6 * s1) (h ^ 4 * w1)")
    print("          (h ^ 2 * b62) b5 b4 b3 b2 b1 (Polynomial.C lambda) =")
    print("        Polynomial.C eta * h ^ 112) :")
    print("    (piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62")
    print("        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval x = 0 := by")
    print("  have h96 : h ^ 96 ≠ 0 := pow_ne_zero 96 hh")
    print("  have hquot :")
    print("      piLeftUnsolvedHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62")
    print("          b5 b4 b3 b2 b1 (Polynomial.C lambda) +")
    print("        h * piLeftUnsolvedTail810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1")
    print("          b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =")
    print("        Polynomial.C eta * h ^ 16 := by")
    print("    apply mul_left_cancel₀ h96")
    print("    rw [← localClearedSixteenthDefect810_left_unsolved_factored]")
    print("    rw [hpower]")
    print("    ring")
    print("  have hev := congrArg (Polynomial.eval x) hquot")
    print("  simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,")
    print("    Polynomial.eval_C, hroot] using hev")
    print()
    print("end PiLeftUnsolvedRootPeel810")
    print()
    print("end Max11DegreeRoutes")


parser = ArgumentParser()
parser.add_argument("part", choices=("header", "block", "footer"))
parser.add_argument("index", nargs="?", type=int)
args = parser.parse_args()

if args.part == "header":
    emit_header()
elif args.part == "block":
    if args.index is None or not 0 <= args.index < BLOCK_COUNT:
        parser.error(f"block index must lie in 0..{BLOCK_COUNT - 1}")
    emit_block(args.index)
else:
    emit_footer()
