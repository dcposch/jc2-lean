#!/usr/bin/env python3
"""Reduce the (8,10) Omicron base head by the exact retained left rows.

All large polynomials are parsed from their Lean definitions.  The only
handwritten formulas are the four small linear solves already present in the
left packet (s1, w1, a4, b5); assertions check those solves before any
reduction is reported.
"""

from hashlib import sha256
import os
from pathlib import Path
import re
import subprocess

import sympy as sp


ROOT = Path(__file__).parent
DEFECT = ROOT / "Fable810ScaleZeroFourteenthDefectScratch.lean"
MU_SOURCE = ROOT / "Fable810ScaleTwoTerminalIntegralBridgeScratch.lean"
NU_SOURCE = ROOT / "Fable810ScaleTwoNuIntegralBridgeScratch.lean"
XI_SOURCE = ROOT / "Fable810ScaleTwoNextIntegralBridgeScratch.lean"


def definition_body(path: Path, name: str) -> str:
    text = path.read_text()
    start = text.index(f"def {name}")
    body_start = text.index(":=", start) + 2
    match = re.search(r"\n(?:end |section |/-!|set_option|/--)", text[body_start:])
    if match is None:
        raise RuntimeError(f"could not find end of {name}")
    return text[body_start : body_start + match.start()]


def parse_literal(body: str, coefficient_type: str, symbols: dict[str, sp.Symbol]):
    pattern = re.compile(
        rf"^\s*([+-]?)\s*\(([0-9]+) : {re.escape(coefficient_type)}\)(.*)$"
    )
    terms = []
    for raw_line in body.splitlines():
        line = raw_line.rstrip()
        if not line:
            continue
        match = pattern.match(line)
        if match is None:
            raise RuntimeError(f"unparsed literal line: {line}")
        sign, coefficient, factors = match.groups()
        scalar = int(coefficient) * (-1 if sign == "-" else 1)
        factors = factors.replace("Polynomial.C lambda", "lam")
        factors = factors.replace(" ^ ", "**")
        terms.append(sp.sympify(f"{scalar}{factors}", locals=symbols))
    return sp.Add(*terms), len(terms)


h, lam = sp.symbols("h lam")
a7, a6, a5, a4, a3, a2, a1, a0 = sp.symbols(
    "a7 a6 a5 a4 a3 a2 a1 a0"
)
b8, b7, b6, b5, b4, b3, b2, b1 = sp.symbols(
    "b8 b7 b6 b5 b4 b3 b2 b1"
)
t0, v1, u1, s1, w1, b62 = sp.symbols("t0 v1 u1 s1 w1 b62")
all_symbols = {
    symbol.name: symbol
    for symbol in (
        h, lam, a7, a6, a5, a4, a3, a2, a1, a0,
        b8, b7, b6, b5, b4, b3, b2, b1,
        t0, v1, u1, s1, w1, b62,
    )
}

numerator, numerator_terms = parse_literal(
    definition_body(DEFECT, "localClearedFifteenthDefect810"),
    "F[X]",
    all_symbols,
)
base_substitution = {
    a7: h**6 * t0,
    a6: h**4 * v1,
    a5: h**2 * u1,
    b8: h**6 * s1,
    b7: h**4 * w1,
    b6: h**2 * b62,
}
base = sp.Poly(sp.expand(numerator.subs(base_substitution)), h)
base_min = min(monomial[0] for monomial, _ in base.terms())
base_head = base.coeff_monomial(h**base_min)

residual_symbols = {symbol.name: symbol for symbol in (t0, v1, u1, b62)}
mu, mu_terms = parse_literal(
    definition_body(MU_SOURCE, "bridgeMuLeftResidual810"),
    "R",
    residual_symbols,
)
nu, nu_terms = parse_literal(
    definition_body(NU_SOURCE, "bridgeNuLeftResidual810"),
    "R",
    residual_symbols,
)
xi, xi_terms = parse_literal(
    definition_body(XI_SOURCE, "bridgeXiLeftResidual810"),
    "R",
    residual_symbols,
)

s_solve = (40 * v1 + 5 * t0**2) / 32
w_solve = (160 * u1 + 40 * t0 * v1 - 5 * t0**3) / 128
a_solve = (
    2048 * b62 - 35 * t0**4 + 240 * t0**2 * v1
    - 640 * t0 * u1 - 320 * v1**2
) / 2560
b_solve = -(
    81920 * a_solve * t0 - 98304 * b62 * t0 + 2912 * t0**5
    - 20480 * t0**3 * v1 + 46080 * t0**2 * u1
    + 30720 * t0 * v1**2 - 40960 * u1 * v1
) / 131072

assert sp.expand(32 * s_solve - 40 * v1 - 5 * t0**2) == 0
assert sp.expand(128 * w_solve - 160 * u1 - 40 * t0 * v1 + 5 * t0**3) == 0
assert sp.expand(
    2560 * a_solve - 2048 * b62 + 35 * t0**4
    - 240 * t0**2 * v1 + 640 * t0 * u1 + 320 * v1**2
) == 0
assert sp.expand(
    81920 * a_solve * t0 + 131072 * b_solve - 98304 * b62 * t0
    + 2912 * t0**5 - 20480 * t0**3 * v1 + 46080 * t0**2 * u1
    + 30720 * t0 * v1**2 - 40960 * u1 * v1
) == 0

reduced_head = sp.cancel(
    base_head.subs({s1: s_solve, w1: w_solve, a4: a_solve, b5: b_solve})
)
reduced_poly = sp.Poly(reduced_head, t0, v1, u1, b62, domain=sp.QQ)
cleared, denominator = sp.fraction(reduced_poly.as_expr())
cleared_poly = sp.Poly(sp.expand(cleared), t0, v1, u1, b62, domain=sp.QQ)

print(f"DEFECT_SHA256={sha256(DEFECT.read_bytes()).hexdigest()}")
print(f"MU_SHA256={sha256(MU_SOURCE.read_bytes()).hexdigest()}")
print(f"NU_SHA256={sha256(NU_SOURCE.read_bytes()).hexdigest()}")
print(f"XI_SHA256={sha256(XI_SOURCE.read_bytes()).hexdigest()}")
print(f"NUMERATOR_TERMS={numerator_terms} BASE_H_MIN={base_min}")
print(f"RESIDUAL_TERMS mu={mu_terms} nu={nu_terms} xi={xi_terms}")
print(
    f"LEFT_SUBSTITUTED_TERMS={len(cleared_poly.terms())} "
    f"DENOMINATOR={denominator} TOTAL_DEGREE={cleared_poly.total_degree()}"
)
print("LEFT_SUBSTITUTED_FACTOR")
print(sp.factor(cleared_poly.as_expr()))

generators = (t0, v1, u1, b62)
for label, divisors in (
    ("MU_NU_XI", (mu, nu, xi)),
    ("XI_NU_MU", (xi, nu, mu)),
    ("NU_XI_MU", (nu, xi, mu)),
):
    quotients, remainder = sp.reduced(
        cleared_poly.as_expr(), divisors, *generators, domain=sp.QQ
    )
    remainder = sp.Poly(remainder, *generators, domain=sp.QQ)
    print(
        f"REDUCTION={label} QUOTIENT_TERMS="
        f"{','.join(str(len(sp.Poly(q, *generators).terms())) for q in quotients)} "
        f"REMAINDER_TERMS={len(remainder.terms())} "
        f"REMAINDER_TOTAL_DEGREE={remainder.total_degree()}"
    )
    print(f"REMAINDER_{label}")
    print(sp.factor(remainder.as_expr()))

if os.environ.get("COMPUTE_GROEBNER") == "1":
    basis = sp.groebner((mu, nu, xi), *generators, order="grevlex", domain=sp.QQ)
    print(
        f"GROEBNER_SIZE={len(basis.polys)} "
        f"GROEBNER_TERMS={','.join(str(len(poly.terms())) for poly in basis.polys)}"
    )
    quotients, remainder = basis.reduce(cleared_poly.as_expr())
    remainder = sp.Poly(remainder, *generators, domain=sp.QQ)
    print(
        f"GROEBNER_QUOTIENT_TERMS="
        f"{','.join(str(len(sp.Poly(q, *generators).terms())) for q in quotients)} "
        f"GROEBNER_REMAINDER_TERMS={len(remainder.terms())} "
        f"GROEBNER_REMAINDER_TOTAL_DEGREE={remainder.total_degree()}"
    )
    print("GROEBNER_REMAINDER")
    print(sp.factor(remainder.as_expr()))

if os.environ.get("COMPUTE_SINGULAR") == "1":
    def singular(expression) -> str:
        polynomial = sp.Poly(expression, *generators, domain=sp.QQ)
        terms = []
        for monomial, coefficient in polynomial.terms():
            if coefficient.q == 1:
                scalar = str(coefficient.p)
            else:
                scalar = f"({coefficient.p}/{coefficient.q})"
            factors = []
            for variable, power in zip(generators, monomial):
                if power == 0:
                    continue
                factors.append(str(variable) if power == 1 else f"{variable}^{power}")
            terms.append("*".join((scalar, *factors)) if factors else scalar)
        return "+".join(terms).replace("+-", "-")

    basis_dump = "G;" if os.environ.get("EMIT_SINGULAR_BASIS") == "1" else ""
    program = f"""
ring r=0,(t0,v1,u1,b62),dp;
poly mu={singular(mu)};
poly nu={singular(nu)};
poly xi={singular(xi)};
poly head={singular(cleared_poly.as_expr())};
ideal I=mu,nu,xi;
ideal G=std(I);
print(\"SINGULAR_GROEBNER_SIZE=\"+string(size(G)));
{basis_dump}
poly rem=reduce(head,G);
print(\"SINGULAR_REMAINDER_TERMS=\"+string(size(rem)));
print(\"SINGULAR_REMAINDER_BEGIN\");
rem;
print(\"SINGULAR_REMAINDER_END\");
quit;
"""
    if os.environ.get("EMIT_SINGULAR") == "1":
        print("SINGULAR_PROGRAM_BEGIN")
        print(program)
        print("SINGULAR_PROGRAM_END")
    result = subprocess.run(
        ["Singular", "-q"],
        input=program,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    print(f"SINGULAR_EXIT={result.returncode}")
    print(result.stdout)
    if result.returncode != 0 or re.search(r"(?m)^\s*[?]", result.stdout):
        raise SystemExit(result.returncode or 1)
