#!/usr/bin/env python3
"""Derive the missing weight-15 first integral of the (6,10) degree-0 row.

The alpha--iota faces are parsed from their Lean definitions and solved
triangularly for the decic coefficients.  The remaining degree-0 Jacobian
one-form is then made closed by a weighted ansatz in the already proved
weight-11 through weight-14 first integrals kappa, lambda, mu, and nu.
"""

from pathlib import Path
import math
import os
import re
import time

import sympy as sp


ROOT = Path(__file__).parent
started = time.monotonic()


def checkpoint(label: str) -> None:
    print(f"{label}_SECONDS={time.monotonic() - started:.3f}", flush=True)


def definition_body(path: Path, name: str) -> str:
    text = path.read_text()
    start = text.index(f"def {name}")
    body_start = text.index(":=", start) + 2
    match = re.search(r"\n(?:set_option|/--|theorem |end |section |/-!)", text[body_start:])
    if match is None:
        raise RuntimeError(f"could not find end of {name}")
    return text[body_start : body_start + match.start()].strip()


L, A, B, C0, D0, E0 = sp.symbols("L A B C0 D0 E0")
P, Q, R, S0, T0, U0, V0, W0, X0 = sp.symbols("P Q R S0 T0 U0 V0 W0 X0")
base_symbols = (L, A, B, C0, D0, E0, P, Q, R, S0, T0, U0, V0, W0, X0)
locals_map: dict[str, object] = {symbol.name: symbol for symbol in base_symbols}


residual_specs = (
    ("alphaResidual610", ROOT / "LowScale610ScaleTwoSecondFace.lean", (A, P)),
    ("betaResidual610", ROOT / "LowScale610ScaleTwoThirdFace.lean", (L, A, B, Q)),
    ("gammaResidual610", ROOT / "LowScale610ScaleTwoFourthFace.lean", (L, A, B, C0, P, R)),
    ("deltaResidual610", ROOT / "LowScale610ScaleTwoFifthFace.lean", (L, A, B, C0, D0, P, Q, S0)),
    ("epsilonResidual610", ROOT / "LowScale610ScaleTwoSixthFace.lean", (L, A, B, C0, D0, E0, P, Q, R, T0)),
    ("zetaResidual610", ROOT / "LowScale610ScaleTwoSeventhFace.lean", (L, A, B, C0, D0, E0, P, Q, R, S0, U0)),
    ("etaResidual610", ROOT / "Grok610ScaleZeroSeventhDefectScratch.lean", (L, A, B, C0, D0, E0, P, Q, R, S0, T0, V0)),
    ("thetaResidual610", ROOT / "Grok610ScaleZeroEighthDefectScratch.lean", (L, A, B, C0, D0, E0, P, Q, R, S0, T0, U0, W0)),
    ("iotaResidual610", ROOT / "Grok610ScaleZeroNinthDefectScratch.lean", (L, A, B, C0, D0, E0, P, Q, R, S0, T0, U0, V0, X0)),
    ("kappaResidual610", ROOT / "Fable610ScaleZeroTenthDefectScratch.lean", (L, A, B, C0, D0, E0, P, Q, R, S0, T0, U0, V0, W0)),
    ("lambdaResidual610", ROOT / "Fable610ScaleZeroEleventhDefectScratch.lean", (L, A, B, C0, D0, E0, P, Q, R, S0, T0, U0, V0, W0)),
    ("muResidual610", ROOT / "Fable610ScaleZeroTwelfthDefectScratch.lean", (L, A, B, C0, D0, E0, P, Q, R, S0, T0, U0, V0, W0)),
)


def translate_lean_expression(body: str) -> sp.Expr:
    expression = body
    for name, _path, arguments in residual_specs:
        arity = len(arguments)
        pattern = rf"\b{name}\s+" + r"\s+".join([r"([A-Za-z][A-Za-z0-9]*)"] * arity)
        expression = re.sub(
            pattern,
            lambda match, n=name, a=arity: f"{n}(" + ",".join(match.group(i) for i in range(1, a + 1)) + ")",
            expression,
        )
    expression = re.sub(r"\(([-]?[0-9]+)\s*/\s*([0-9]+)\s*:\s*F\)", r"(\1/\2)", expression)
    expression = re.sub(r"\(([-]?[0-9]+)\s*:\s*F\)", r"(\1)", expression)
    expression = expression.replace(" ^ ", "**")
    expression = re.sub(r"\s+", " ", expression)
    return sp.expand(sp.sympify(expression, locals=locals_map))


parsed: dict[str, sp.Expr] = {}
for name, path, formal_arguments in residual_specs:
    expression = translate_lean_expression(definition_body(path, name))
    parsed[name] = expression
    locals_map[name] = lambda *actual, e=expression, formal=formal_arguments: e.subs(dict(zip(formal, actual)))
checkpoint("PARSED")


ca, cb, cg, cd, ce, cz, cet, ct, ci = sp.symbols("ca cb cg cd ce cz cet ct ci")
constant_residuals = (ca, cb, cg, cd, ce, cz, cet, ct, ci)
triangular = (
    ("alphaResidual610", P, ca),
    ("betaResidual610", Q, cb),
    ("gammaResidual610", R, cg),
    ("deltaResidual610", S0, cd),
    ("epsilonResidual610", T0, ce),
    ("zetaResidual610", U0, cz),
    ("etaResidual610", V0, cet),
    ("thetaResidual610", W0, ct),
    ("iotaResidual610", X0, ci),
)

solved: dict[sp.Symbol, sp.Expr] = {}
for name, coordinate, residual_constant in triangular:
    equation = sp.expand(parsed[name].subs(solved) - residual_constant)
    solution = sp.solve(equation, coordinate, dict=False)
    if len(solution) != 1:
        raise RuntimeError(f"{name} was not triangular in {coordinate}")
    solved[coordinate] = sp.expand(solution[0])
    assert sp.expand(parsed[name].subs(solved) - residual_constant) == 0
checkpoint("TRIANGULAR")


# Reconstruct the canonical weight-14 fourth-tail residual independently
# from the same formal Faber sum used by derive_610_nu_residual.py.
t = sp.symbols("t")
u = A * t**2 + B * t**3 + C0 * t**4 + D0 * t**5 + E0 * t**6
alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota = sp.symbols(
    "alpha beta gamma delta epsilon zeta eta theta iota"
)
basis = (
    (10, sp.Rational(5, 3), 1),
    (9, sp.Rational(3, 2), L),
    (8, sp.Rational(4, 3), alpha),
    (7, sp.Rational(7, 6), beta),
    (6, sp.Integer(1), gamma),
    (5, sp.Rational(5, 6), delta),
    (4, sp.Rational(2, 3), epsilon),
    (3, sp.Rational(1, 2), zeta),
    (2, sp.Rational(1, 3), eta),
    (1, sp.Rational(1, 6), theta),
    (0, sp.Integer(0), iota),
)


def binomial_series(power: sp.Rational, degree: int) -> sp.Expr:
    return sp.expand(sum(sp.binomial(power, exponent) * u**exponent
                         for exponent in range(degree // 2 + 1)))


def coefficient_below_zero(depth: int) -> sp.Expr:
    answer = 0
    for leading_degree, power, scalar in basis:
        target = leading_degree + depth
        answer += scalar * binomial_series(power, target).coeff(t, target)
    return sp.expand(answer)


faber_constants = {
    alpha: ca, beta: cb, gamma: cg, delta: cd, epsilon: ce,
    zeta: cz, eta: cet, theta: ct, iota: ci,
}
kappa = sp.expand(parsed["kappaResidual610"].subs(solved))
lambda_residual = sp.expand(parsed["lambdaResidual610"].subs(solved))
mu = sp.expand(parsed["muResidual610"].subs(solved))
raw_fourth = coefficient_below_zero(4).subs(faber_constants)
nu = sp.expand(raw_fourth + B * kappa / 6 + A * lambda_residual / 3)
checkpoint("INVARIANTS")


dynamic = (A, B, C0, D0, E0)
W = solved[W0]
X = solved[X0]
omega = tuple(sp.expand((W if variable == E0 else 0) - D0 * sp.diff(X, variable))
              for variable in dynamic)

weights = {
    L: 1, A: 2, B: 3, C0: 4, D0: 5, E0: 6,
    ca: 2, cb: 3, cg: 4, cd: 5, ce: 6, cz: 7, cet: 8, ct: 9, ci: 10,
}
weighted_generators = tuple(weights)


def monomials_of_weight(target: int) -> tuple[sp.Expr, ...]:
    output: list[sp.Expr] = []

    def visit(index: int, remaining: int, current: sp.Expr) -> None:
        if remaining == 0:
            output.append(current)
            return
        if index == len(weighted_generators):
            return
        variable = weighted_generators[index]
        weight = weights[variable]
        for power in range(remaining // weight + 1):
            visit(index + 1, remaining - power * weight, current * variable**power)

    visit(0, target, sp.Integer(1))
    return tuple(output)


multiplier_data = (
    (kappa, monomials_of_weight(4), "m_kappa"),
    (lambda_residual, monomials_of_weight(3), "m_lambda"),
    (mu, monomials_of_weight(2), "m_mu"),
    (nu, monomials_of_weight(1), "m_nu"),
)
unknowns: list[sp.Symbol] = []
corrected = list(omega)
multipliers: list[tuple[str, sp.Expr]] = []
for invariant, monomials, label in multiplier_data:
    coefficients = sp.symbols(f"{label}_0:{len(monomials)}")
    unknowns.extend(coefficients)
    multiplier = sp.Add(*(coefficient * monomial for coefficient, monomial in zip(coefficients, monomials)))
    multipliers.append((label, multiplier))
    for index, variable in enumerate(dynamic):
        corrected[index] += multiplier * sp.diff(invariant, variable)
corrected = [sp.expand(component) for component in corrected]
checkpoint("CORRECTED_FORM")


closure_coefficients: list[sp.Expr] = []
coefficient_generators = (*dynamic, L, *constant_residuals)
for i, variable_i in enumerate(dynamic):
    for j in range(i):
        closure = sp.expand(sp.diff(corrected[i], dynamic[j]) - sp.diff(corrected[j], variable_i))
        closure_coefficients.extend(sp.Poly(closure, *coefficient_generators).coeffs())
checkpoint("CLOSURE_COEFFICIENTS")

matrix, rhs = sp.linear_eq_to_matrix(closure_coefficients, unknowns)
checkpoint("CLOSURE_MATRIX")
solutions = list(sp.linsolve((matrix, rhs), unknowns))
if len(solutions) != 1:
    raise RuntimeError(f"expected one affine solution family, got {len(solutions)}")
solution_tuple = solutions[0]
free = set().union(*(entry.free_symbols for entry in solution_tuple)) & set(unknowns)
solution = {
    unknown: sp.expand(value.subs({symbol: 0 for symbol in free}))
    for unknown, value in zip(unknowns, solution_tuple)
}
corrected = [sp.expand(component.subs(solution)) for component in corrected]
checkpoint("CLOSURE_SOLVED")


integral = sp.Integer(0)
for variable, component in zip(dynamic, corrected):
    remainder = sp.expand(component - sp.diff(integral, variable))
    integral = sp.expand(integral + sp.integrate(remainder, variable))
assert all(sp.expand(sp.diff(integral, variable) - component) == 0
           for variable, component in zip(dynamic, corrected))
checkpoint("INTEGRATED")

print("PARSED_RESIDUALS=" + ",".join(name for name, _path, _arguments in residual_specs))
print("TRIANGULAR_SOLVES=" + ",".join(str(coordinate) for _name, coordinate, _constant in triangular))
print("MULTIPLIER_BASE_SIZES=" + ",".join(str(len(monomials)) for _invariant, monomials, _label in multiplier_data))
print(f"CLOSURE_MATRIX={matrix.rows}x{matrix.cols}")
print(f"FREE_PARAMETERS={len(free)}")
for label, multiplier in multipliers:
    print(f"CORRECTION_{label.upper()}={sp.factor(multiplier.subs(solution))}")
print(f"DEGREE_ZERO_TERMS={len(sp.Poly(integral, *coefficient_generators).terms())}")
print("DEGREE_ZERO_RESIDUAL_BEGIN")
print(sp.factor(integral))
print("DEGREE_ZERO_RESIDUAL_END")

if os.environ.get("EMIT_GROUPS") == "1":
    constant_part = integral
    for residual_constant in constant_residuals:
        coefficient = sp.expand(sp.diff(integral, residual_constant))
        if any(other in coefficient.free_symbols for other in constant_residuals):
            raise RuntimeError("degree-zero residual is nonlinear in old residuals")
        if coefficient != 0:
            print(
                f"DEGREE_ZERO_GROUP_{residual_constant} "
                f"TERMS={len(sp.Poly(coefficient, *dynamic, L).terms())}"
            )
            print(sp.factor(coefficient))
            constant_part -= residual_constant * coefficient
    constant_part = sp.expand(constant_part)
    print(
        f"DEGREE_ZERO_GROUP_BASE "
        f"TERMS={len(sp.Poly(constant_part, *dynamic, L).terms())}"
    )
    print(sp.factor(constant_part))

if os.environ.get("COMPUTE_SOURCE") == "1":
    residual_substitution = {
        residual_constant: parsed[name]
        for residual_constant, (name, _path, _arguments) in zip(
            constant_residuals, residual_specs
        )
    }
    native_integral = sp.expand(integral.subs(residual_substitution))
    native_polynomial = sp.Poly(native_integral, *base_symbols, domain=sp.QQ)
    coordinate_weights = dict(zip(base_symbols, (1, 2, 3, 4, 5, 6, 2, 3, 4, 5, 6, 7, 8, 9, 10)))
    native_weights = {
        sum(coordinate_weights[coordinate] * exponent
            for coordinate, exponent in zip(base_symbols, monomial))
        for monomial, _coefficient in native_polynomial.terms()
    }
    if native_weights != {15}:
        raise RuntimeError(f"native residual has unexpected weights {native_weights}")
    print(f"DEGREE_ZERO_NATIVE_TERMS={len(native_polynomial.terms())}")

    h, lam = sp.symbols("h lam")
    a5, a4, a3, a2, a1, a0 = sp.symbols("a5 a4 a3 a2 a1 a0")
    b8, b7, b6, b5, b4, b3, b2, b1, b0 = sp.symbols(
        "b8 b7 b6 b5 b4 b3 b2 b1 b0"
    )
    AA, BB, CC, DD, EE, PP, QQ, RR, SS, TT, UU, VV, WW, XX = sp.symbols(
        "AA BB CC DD EE PP QQ RR SS TT UU VV WW XX"
    )
    compact_substitution = {
        L: -lam / 3,
        A: AA / 12, B: BB / 54, C0: CC / 144,
        D0: DD / 324, E0: EE / 46656,
        P: PP / 4, Q: QQ / 9, R: RR / 432, S0: SS / 216,
        T0: TT / 7776, U0: UU / 11664, V0: VV / 186624,
        W0: WW / 5038848, X0: XX / 60466176,
    }
    compact_rational = sp.Poly(
        sp.expand(native_integral.subs(compact_substitution)),
        AA, BB, CC, DD, EE, PP, QQ, RR, SS, TT, UU, VV, WW, XX, lam,
        domain=sp.QQ,
    )
    clearing_coefficient = math.lcm(*(coefficient.q for coefficient in compact_rational.coeffs()))
    compact = sp.Poly(
        sp.expand(clearing_coefficient * compact_rational.as_expr()),
        *compact_rational.gens,
        domain=sp.ZZ,
    )
    print(
        f"DEGREE_ZERO_COMPACT_TERMS={len(compact.terms())} "
        f"CLEARING={clearing_coefficient} CONTENT={compact.content()}"
    )

    Abar = 12 * a4 * h**6 - 5 * a5**2
    Bbar = 54 * a3 * h**12 - 36 * a4 * a5 * h**6 + 10 * a5**3
    Cbar = 144 * a2 * h**18 - 72 * a3 * a5 * h**12 + 24 * a4 * a5**2 * h**6 - 5 * a5**4
    Dbar = 324 * a1 * h**24 - 108 * a2 * a5 * h**18 + 27 * a3 * a5**2 * h**12 - 6 * a4 * a5**3 * h**6 + a5**5
    Ebar = 46656 * a0 * h**30 - 7776 * a1 * a5 * h**24 + 1296 * a2 * a5**2 * h**18 - 216 * a3 * a5**3 * h**12 + 36 * a4 * a5**4 * h**6 - 5 * a5**6
    Pbar = -5 * a5**2 + 2 * lam * a5 * h**5 + 4 * b8 * h**2
    Qbar = 10 * a5**3 - 3 * lam * a5**2 * h**5 - 12 * a5 * b8 * h**2 + 9 * b7 * h**8
    Rbar = -210 * a5**4 + 56 * lam * a5**3 * h**5 + 336 * a5**2 * b8 * h**2 - 504 * a5 * b7 * h**8 + 432 * b6 * h**14
    Sbar = 28 * a5**5 - 7 * lam * a5**4 * h**5 - 56 * a5**3 * b8 * h**2 + 126 * a5**2 * b7 * h**8 - 216 * a5 * b6 * h**14 + 216 * b5 * h**20
    Tbar = -175 * a5**6 + 42 * lam * a5**5 * h**5 + 420 * a5**4 * b8 * h**2 - 1260 * a5**3 * b7 * h**8 + 3240 * a5**2 * b6 * h**14 - 6480 * a5 * b5 * h**20 + 7776 * b4 * h**26
    Ubar = 30 * a5**7 - 7 * lam * a5**6 * h**5 - 84 * a5**5 * b8 * h**2 + 315 * a5**4 * b7 * h**8 - 1080 * a5**3 * b6 * h**14 + 3240 * a5**2 * b5 * h**20 - 7776 * a5 * b4 * h**26 + 11664 * b3 * h**32
    Vbar = -35 * a5**8 + 8 * lam * a5**7 * h**5 + 112 * a5**6 * b8 * h**2 - 504 * a5**5 * b7 * h**8 + 2160 * a5**4 * b6 * h**14 - 8640 * a5**3 * b5 * h**20 + 31104 * a5**2 * b4 * h**26 - 93312 * a5 * b3 * h**32 + 186624 * b2 * h**38
    Wbar = 40 * a5**9 - 9 * lam * a5**8 * h**5 - 144 * a5**7 * b8 * h**2 + 756 * a5**6 * b7 * h**8 - 3888 * a5**5 * b6 * h**14 + 19440 * a5**4 * b5 * h**20 - 93312 * a5**3 * b4 * h**26 + 419904 * a5**2 * b3 * h**32 - 1679616 * a5 * b2 * h**38 + 5038848 * b1 * h**44
    Xbar = -9 * a5**10 + 2 * lam * a5**9 * h**5 + 36 * a5**8 * b8 * h**2 - 216 * a5**7 * b7 * h**8 + 1296 * a5**6 * b6 * h**14 - 7776 * a5**5 * b5 * h**20 + 46656 * a5**4 * b4 * h**26 - 279936 * a5**3 * b3 * h**32 + 1679616 * a5**2 * b2 * h**38 - 10077696 * a5 * b1 * h**44 + 60466176 * b0 * h**50
    source_substitution = {
        L: -lam / 3,
        A: Abar / (12 * h**10), B: Bbar / (54 * h**15),
        C0: Cbar / (144 * h**20), D0: Dbar / (324 * h**25),
        E0: Ebar / (46656 * h**30), P: Pbar / (4 * h**10),
        Q: Qbar / (9 * h**15), R: Rbar / (432 * h**20),
        S0: Sbar / (216 * h**25), T0: Tbar / (7776 * h**30),
        U0: Ubar / (11664 * h**35), V0: Vbar / (186624 * h**40),
        W0: Wbar / (5038848 * h**45), X0: Xbar / (60466176 * h**50),
    }
    cleared_rational = sp.cancel(clearing_coefficient * h**75 * native_integral.subs(source_substitution))
    cleared_numerator, cleared_denominator = sp.fraction(cleared_rational)
    if cleared_denominator != 1:
        raise RuntimeError(f"source clearing retained denominator {cleared_denominator}")
    cleared = sp.Poly(sp.expand(cleared_numerator), h)
    print(
        f"DEGREE_ZERO_CLEARED_H_LEVELS={len(cleared.terms())} "
        f"H_MIN={min(monomial[0] for monomial, _coefficient in cleared.terms())}"
    )

    w1, a42, p32, p21, p1, p0 = sp.symbols("w1 a42 p32 p21 p1 p0")
    s2, u2, b63, q53, q41, q3, q2, q1, q0 = sp.symbols(
        "s2 u2 b63 q53 q41 q3 q2 q1 q0"
    )
    post_collapse_jet = {
        a5: h**5 * w1, a4: h**4 * a42, a3: h**2 * p32,
        a2: h * p21, a1: p1, a0: p0,
        b8: h**8 * s2, b7: h**6 * u2, b6: h**5 * b63,
        b5: h**3 * q53, b4: h * q41, b3: q3, b2: q2,
        b1: q1, b0: q0,
    }
    jet = sp.Poly(sp.expand(cleared.as_expr().subs(post_collapse_jet)), h)
    jet_minimum = min(monomial[0] for monomial, _coefficient in jet.terms())
    jet_head = sp.factor(jet.coeff_monomial(h**jet_minimum))
    print(
        f"DEGREE_ZERO_POST_COLLAPSE_H_MIN={jet_minimum} "
        f"H_LEVELS={len(jet.terms())} "
        f"HEAD_TERMS={len(sp.Add.make_args(sp.expand(jet_head)))}"
    )
    print("DEGREE_ZERO_POST_COLLAPSE_HEAD_BEGIN")
    print(jet_head)
    print("DEGREE_ZERO_POST_COLLAPSE_HEAD_END")
