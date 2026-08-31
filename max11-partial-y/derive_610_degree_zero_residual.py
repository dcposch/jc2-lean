#!/usr/bin/env python3
"""Derive the missing weight-15 first integral of the (6,10) degree-0 row.

The alpha--iota faces are parsed from their Lean definitions and solved
triangularly for the decic coefficients.  The remaining degree-0 Jacobian
one-form is then made closed by a weighted ansatz in the already proved
weight-11 through weight-14 first integrals kappa, lambda, mu, and nu.
"""

from pathlib import Path
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
