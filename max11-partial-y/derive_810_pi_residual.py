#!/usr/bin/env python3
"""Derive the missing weight-16 first integral of the (8,10) degree-1 row.

The residual definitions are parsed from their Lean sources.  We solve the
triangular alpha--iota definitions for the decic coefficients, substitute
them into the degree-1 differential Jacobian row, and make that polynomial
one-form closed using a weighted ansatz in d(kappa), d(mu), d(nu), d(xi),
and d(omicron).  The solved d(omicron) multiplier is zero, leaving exactly
the four correction multipliers used by the formal Lean identity.
"""

from pathlib import Path
from hashlib import sha256
import os
import re

import sympy as sp


ROOT = Path(__file__).parent


def definition_body(path: Path, name: str) -> str:
    text = path.read_text()
    start = text.index(f"def {name}")
    body_start = text.index(":=", start) + 2
    match = re.search(r"\n(?:set_option|/--|theorem |end |section |/-!)", text[body_start:])
    if match is None:
        raise RuntimeError(f"could not find end of {name}")
    return text[body_start : body_start + match.start()].strip()


L, A, B, C0, D0, E0, F0, G0 = sp.symbols("L A B C0 D0 E0 F0 G0")
P, Q, R, S0, T0, U0, V0, W0, X0 = sp.symbols("P Q R S0 T0 U0 V0 W0 X0")
base_symbols = (L, A, B, C0, D0, E0, F0, G0, P, Q, R, S0, T0, U0, V0, W0, X0)
locals_map: dict[str, object] = {symbol.name: symbol for symbol in base_symbols}


residual_specs = (
    ("alphaResidual810", ROOT / "LowScale810ScaleTwoSecondFace.lean", (A, P)),
    ("betaResidual810", ROOT / "LowScale810ScaleTwoThirdFace.lean", (L, A, B, Q)),
    ("gammaResidual810", ROOT / "LowScale810ScaleTwoFourthFace.lean", (L, A, B, C0, P, R)),
    ("deltaResidual810", ROOT / "LowScale810ScaleTwoFifthFace.lean", (L, A, B, C0, D0, P, Q, S0)),
    ("epsilonResidual810", ROOT / "LowScale810ScaleTwoSixthFace.lean", (L, A, B, C0, D0, E0, P, Q, R, T0)),
    ("zetaResidual810", ROOT / "LowScale810ScaleTwoSeventhFace.lean", (L, A, B, C0, D0, E0, F0, P, Q, R, S0, U0)),
    ("etaResidual810", ROOT / "LowScale810ScaleTwoEighthFace.lean", (L, A, B, C0, D0, E0, F0, G0, P, Q, R, S0, T0, V0)),
    ("thetaResidual810", ROOT / "Grok810ScaleZeroEighthDefectScratch.lean", (L, A, B, C0, D0, E0, F0, G0, P, Q, R, S0, T0, U0, W0)),
    ("iotaResidual810", ROOT / "Grok810ScaleZeroNinthDefectScratch.lean", (L, A, B, C0, D0, E0, F0, G0, P, Q, R, S0, T0, U0, V0, X0)),
    ("kappaResidual810", ROOT / "Grok810ScaleZeroTenthDefectScratch.lean", (L, A, B, C0, D0, E0, F0, G0, P, Q, R, S0, T0, U0, V0, W0)),
    ("muResidual810", ROOT / "Fable810ScaleZeroEleventhDefectScratch.lean", (L, A, B, C0, D0, E0, F0, G0, P, Q, R, S0, T0, U0, V0, W0)),
    ("nuResidual810", ROOT / "Fable810ScaleZeroTwelfthDefectScratch.lean", (L, A, B, C0, D0, E0, F0, G0, P, Q, R, S0, T0, U0, V0, W0)),
    ("xiResidual810", ROOT / "Fable810ScaleZeroThirteenthDefectScratch.lean", (L, A, B, C0, D0, E0, F0, G0, P, Q, R, S0, T0, U0, V0, W0)),
    ("omicronResidual810", ROOT / "Fable810ScaleZeroFourteenthDefectScratch.lean", (L, A, B, C0, D0, E0, F0, G0, P, Q, R, S0, T0, U0, V0, W0)),
)


def translate_lean_expression(body: str) -> sp.Expr:
    expression = body
    # Every residual call in these definitions has plain identifier arguments.
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


def parse_literal_definition(
    path: Path, name: str, coefficient_type: str, symbols: dict[str, sp.Symbol]
) -> tuple[sp.Expr, int]:
    pattern = re.compile(
        rf"^\s*([+-]?)\s*\(([0-9]+) : {re.escape(coefficient_type)}\)(.*)$"
    )
    terms: list[sp.Expr] = []
    for raw_line in definition_body(path, name).splitlines():
        line = raw_line.rstrip()
        if not line:
            continue
        match = pattern.match(line)
        if match is None:
            raise RuntimeError(f"unparsed literal line in {name}: {line}")
        sign, coefficient, factors = match.groups()
        scalar = int(coefficient) * (-1 if sign == "-" else 1)
        factors = factors.replace(" ^ ", "**")
        terms.append(sp.sympify(f"{scalar}{factors}", locals=symbols))
    return sp.Add(*terms), len(terms)


parsed: dict[str, sp.Expr] = {}
for name, path, formal_arguments in residual_specs:
    body = definition_body(path, name)
    expression = translate_lean_expression(body)
    parsed[name] = expression
    locals_map[name] = lambda *actual, e=expression, formal=formal_arguments: e.subs(dict(zip(formal, actual)))


ca, cb, cg, cd, ce, cz, cet, ct, ci, ck = sp.symbols("ca cb cg cd ce cz cet ct ci ck")
constant_residuals = (ca, cb, cg, cd, ce, cz, cet, ct, ci, ck)
triangular = (
    ("alphaResidual810", P, ca),
    ("betaResidual810", Q, cb),
    ("gammaResidual810", R, cg),
    ("deltaResidual810", S0, cd),
    ("epsilonResidual810", T0, ce),
    ("zetaResidual810", U0, cz),
    ("etaResidual810", V0, cet),
    ("thetaResidual810", W0, ct),
    ("iotaResidual810", X0, ci),
)

solved: dict[sp.Symbol, sp.Expr] = {}
for name, coordinate, residual_constant in triangular:
    equation = sp.expand(parsed[name].subs(solved) - residual_constant)
    solution = sp.solve(equation, coordinate, dict=False)
    if len(solution) != 1:
        raise RuntimeError(f"{name} was not triangular in {coordinate}")
    solved[coordinate] = sp.expand(solution[0])
    assert sp.expand(parsed[name].subs(solved) - residual_constant) == 0


dynamic = (A, B, C0, D0, E0, F0, G0)
kappa = sp.expand(parsed["kappaResidual810"].subs(solved))
mu = sp.expand(parsed["muResidual810"].subs(solved))
nu = sp.expand(parsed["nuResidual810"].subs(solved))
xi = sp.expand(parsed["xiResidual810"].subs(solved))
omicron = sp.expand(parsed["omicronResidual810"].subs(solved))

V = solved[V0]
W = solved[W0]
X = solved[X0]
omega = tuple(
    sp.expand(
        (2 * V if variable == G0 else 0)
        + (W if variable == F0 else 0)
        - F0 * sp.diff(W, variable)
        - 2 * E0 * sp.diff(X, variable)
    )
    for variable in dynamic
)


weights = {
    L: 1, A: 2, B: 3, C0: 4, D0: 5, E0: 6, F0: 7, G0: 8,
    ca: 2, cb: 3, cg: 4, cd: 5, ce: 6, cz: 7, cet: 8, ct: 9, ci: 10,
    ck: 11,
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
    (kappa, monomials_of_weight(5), "m_kappa"),
    (mu, monomials_of_weight(4), "m_mu"),
    (nu, monomials_of_weight(3), "m_nu"),
    (xi, monomials_of_weight(2), "m_xi"),
    (omicron, monomials_of_weight(1), "m_omicron"),
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


closure_coefficients: list[sp.Expr] = []
coefficient_generators = (*dynamic, L, *constant_residuals)
for i, variable_i in enumerate(dynamic):
    for j in range(i):
        closure = sp.expand(sp.diff(corrected[i], dynamic[j]) - sp.diff(corrected[j], variable_i))
        closure_coefficients.extend(sp.Poly(closure, *coefficient_generators).coeffs())

matrix, rhs = sp.linear_eq_to_matrix(closure_coefficients, unknowns)
solution_set = sp.linsolve((matrix, rhs), unknowns)
solutions = list(solution_set)
if len(solutions) != 1:
    raise RuntimeError(f"expected one affine solution family, got {len(solutions)}")
solution_tuple = solutions[0]
free = set().union(*(entry.free_symbols for entry in solution_tuple)) & set(unknowns)
zero_free = {symbol: 0 for symbol in free}
solution = {unknown: sp.expand(value.subs(zero_free)) for unknown, value in zip(unknowns, solution_tuple)}
corrected = [sp.expand(component.subs(solution)) for component in corrected]


integral = sp.Integer(0)
for variable, component in zip(dynamic, corrected):
    remainder = sp.expand(component - sp.diff(integral, variable))
    integral = sp.expand(integral + sp.integrate(remainder, variable))
assert all(sp.expand(sp.diff(integral, variable) - component) == 0 for variable, component in zip(dynamic, corrected))

print("PARSED_RESIDUALS=" + ",".join(name for name, _path, _arguments in residual_specs))
print("TRIANGULAR_SOLVES=" + ",".join(str(coordinate) for _name, coordinate, _constant in triangular))
print(f"KAPPA_TERMS={len(sp.Poly(kappa, *coefficient_generators).terms())}")
print(f"MU_TERMS={len(sp.Poly(mu, *coefficient_generators).terms())}")
print(f"NU_TERMS={len(sp.Poly(nu, *coefficient_generators).terms())}")
print(f"XI_TERMS={len(sp.Poly(xi, *coefficient_generators).terms())}")
print(f"OMICRON_TERMS={len(sp.Poly(omicron, *coefficient_generators).terms())}")
print("MULTIPLIER_BASE_SIZES=" + ",".join(str(len(monomials)) for _invariant, monomials, _label in multiplier_data))
print(f"CLOSURE_MATRIX={matrix.rows}x{matrix.cols} RANK={matrix.rank()}")
print(f"FREE_PARAMETERS={len(free)}")
for label, multiplier in multipliers:
    print(f"CORRECTION_{label.upper()}={sp.factor(multiplier.subs(solution))}")
print(f"PI_TERMS={len(sp.Poly(integral, *coefficient_generators).terms())}")
print("PI_RESIDUAL_BEGIN")
print(sp.factor(integral))
print("PI_RESIDUAL_END")
if os.environ.get("EMIT_GROUPS") == "1":
    residual_polynomial = sp.Poly(integral, *constant_residuals)
    print(f"PI_RESIDUAL_CONSTANT_DEGREE={residual_polynomial.total_degree()}")
    constant_part = integral
    for residual_constant in constant_residuals:
        coefficient = sp.expand(sp.diff(integral, residual_constant))
        if coefficient != 0:
            print(
                f"PI_GROUP_{residual_constant} TERMS="
                f"{len(sp.Poly(coefficient, *dynamic, L).terms())}"
            )
            print(sp.factor(coefficient))
            constant_part -= residual_constant * coefficient
    constant_part = sp.expand(constant_part)
    print(f"PI_GROUP_BASE TERMS={len(sp.Poly(constant_part, *dynamic, L).terms())}")
    print(sp.factor(constant_part))

if os.environ.get("COMPUTE_NATIVE") == "1" or os.environ.get("COMPUTE_CLEARING") == "1":
    residual_substitution = {
        residual_constant: parsed[name]
        for residual_constant, (name, _path, _arguments) in zip(
            constant_residuals, residual_specs
        )
    }
    native_integral = sp.expand(integral.subs(residual_substitution))
    native_polynomial = sp.Poly(native_integral, *base_symbols)
    print(f"PI_NATIVE_TERMS={len(native_polynomial.terms())}")
    if os.environ.get("COMPUTE_NATIVE") == "1":
        print("PI_NATIVE_BEGIN")
        print(sp.factor(native_integral))
        print("PI_NATIVE_END")

if os.environ.get("COMPUTE_CLEARING") == "1":
    h, lam = sp.symbols("h lam")
    a7, a6, a5, a4, a3, a2, a1, a0 = sp.symbols(
        "a7 a6 a5 a4 a3 a2 a1 a0"
    )
    b9, b8, b7, b6, b5, b4, b3, b2, b1 = sp.symbols(
        "b9 b8 b7 b6 b5 b4 b3 b2 b1"
    )
    source_symbols = (
        h, lam, a7, a6, a5, a4, a3, a2, a1, a0,
        b8, b7, b6, b5, b4, b3, b2, b1,
    )
    octic_coefficients = {
        7: a7, 6: a6, 5: a5, 4: a4, 3: a3, 2: a2, 1: a1, 0: a0,
    }
    decic_coefficients = {
        9: b9, 8: b8, 7: b7, 6: b6, 5: b5,
        4: b4, 3: b3, 2: b2, 1: b1,
    }
    depression_center = a7 / (8 * h**7)
    ninth_face = {b9: (5 * a7 * h**2 - lam * h**9) / 4}

    def depressed_coordinate(
        degree: int, depth: int, coefficients: dict[int, sp.Symbol]
    ) -> sp.Expr:
        expression = sp.binomial(degree, depth) * (-depression_center) ** depth
        for source_depth in range(1, depth + 1):
            source_degree = degree - source_depth
            expression += (
                sp.binomial(source_degree, depth - source_depth)
                * coefficients[source_degree]
                / h**source_degree
                * (-depression_center) ** (depth - source_depth)
            )
        return sp.cancel(expression.subs(ninth_face))

    coordinate_depths = {
        L: 1,
        A: 2, B: 3, C0: 4, D0: 5, E0: 6, F0: 7, G0: 8,
        P: 2, Q: 3, R: 4, S0: 5, T0: 6, U0: 7, V0: 8, W0: 9,
    }
    coordinate_weights = {**coordinate_depths, X0: 10}
    octic_coordinates = (A, B, C0, D0, E0, F0, G0)
    cleared_coordinates: dict[sp.Symbol, sp.Expr] = {}
    for coordinate, depth in coordinate_depths.items():
        degree = 8 if coordinate in octic_coordinates else 10
        coefficients = octic_coefficients if degree == 8 else decic_coefficients
        depressed = depressed_coordinate(degree, depth, coefficients)
        cleared = sp.cancel(depressed * h ** (7 * depth))
        cleared_numerator, cleared_denominator = sp.fraction(cleared)
        if h in cleared_denominator.free_symbols:
            raise RuntimeError(f"h remained in cleared denominator of {coordinate}")
        cleared_coordinates[coordinate] = cleared
        print(
            f"CLEARED_COORDINATE={coordinate} WEIGHT={depth} "
            f"TERMS={len(sp.Poly(cleared_numerator, *source_symbols).terms())} "
            f"DENOMINATOR={cleared_denominator}"
        )

    for monomial, _coefficient in native_polynomial.terms():
        monomial_weight = sum(
            exponent * coordinate_weights[coordinate]
            for coordinate, exponent in zip(base_symbols, monomial)
        )
        if monomial_weight != 16:
            raise RuntimeError(f"native pi term has weight {monomial_weight}, not 16")

    cleared_pi = sp.expand(native_integral.xreplace(cleared_coordinates))
    cleared_pi_rational_polynomial = sp.Poly(cleared_pi, *source_symbols)
    clearing_scale, cleared_pi_polynomial = (
        cleared_pi_rational_polynomial.clear_denoms(convert=True)
    )
    cleared_pi_numerator = cleared_pi_polynomial.as_expr()
    print(
        f"PI_CLEARING_WEIGHT=112 TERMS={len(cleared_pi_polynomial.terms())} "
        f"SCALE={clearing_scale} "
        f"CONTENT={cleared_pi_polynomial.content()}"
    )

    t0, v1, u1, s1, w1, b62 = sp.symbols("t0 v1 u1 s1 w1 b62")
    left_jet_substitution = {
        a7: h**6 * t0,
        a6: h**4 * v1,
        a5: h**2 * u1,
        b8: h**6 * s1,
        b7: h**4 * w1,
        b6: h**2 * b62,
    }
    left_jet = sp.Poly(
        sp.expand(cleared_pi_numerator.subs(left_jet_substitution)), h
    )
    left_minimum = min(monomial[0] for monomial, _coefficient in left_jet.terms())
    left_head = sp.expand(left_jet.coeff_monomial(h**left_minimum))
    left_head_symbols = (
        t0, v1, u1, s1, w1, b62,
        a4, a3, a2, a1, a0, b5, b4, b3, b2, b1, lam,
    )
    left_head_polynomial = sp.Poly(left_head, *left_head_symbols)
    print(
        f"PI_LEFT_H_MIN={left_minimum} "
        f"HEAD_TERMS={len(left_head_polynomial.terms())} "
        f"HEAD_TOTAL_DEGREE={left_head_polynomial.total_degree()}"
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

    reduced_left_head = sp.cancel(
        left_head.subs({s1: s_solve, w1: w_solve, a4: a_solve, b5: b_solve})
    )
    reduced_left_rational = sp.Poly(
        reduced_left_head, t0, v1, u1, b62, domain=sp.QQ
    )
    reduced_left_scale, reduced_left_polynomial = (
        reduced_left_rational.clear_denoms(convert=True)
    )
    print(
        f"PI_LEFT_REDUCED_TERMS={len(reduced_left_polynomial.terms())} "
        f"SCALE={reduced_left_scale} "
        f"TOTAL_DEGREE={reduced_left_polynomial.total_degree()}"
    )
    if os.environ.get("EMIT_JET_PROFILE") == "1":
        solved_left_jet = sp.Poly(
            sp.expand(
                left_jet.as_expr().subs(
                    {s1: s_solve, w1: w_solve, a4: a_solve, b5: b_solve}
                )
            ),
            h,
        )
        jet_exponents = sorted(
            monomial[0] for monomial, _coefficient in solved_left_jet.terms()
        )
        print(
            f"PI_LEFT_SOLVED_H_EXPONENTS={','.join(str(exponent) for exponent in jet_exponents)}"
        )
        top_variables = {t0, v1, u1, b62}
        for exponent in jet_exponents:
            coefficient = sp.expand(solved_left_jet.coeff_monomial(h**exponent))
            coefficient_variables = coefficient.free_symbols
            coefficient_polynomial = sp.Poly(
                coefficient,
                *(
                    t0, v1, u1, b62,
                    a3, a2, a1, a0, b4, b3, b2, b1, lam,
                ),
            )
            fresh_variables = sorted(
                str(variable) for variable in coefficient_variables - top_variables
            )
            print(
                f"PI_LEFT_JET_H={exponent} TERMS={len(coefficient_polynomial.terms())} "
                f"FRESH={','.join(fresh_variables) if fresh_variables else '-'}"
            )
            if os.environ.get("EMIT_JET_EXPRESSIONS") == "1":
                print(f"PI_LEFT_JET_H_{exponent}_BEGIN")
                print(sp.factor(coefficient))
                print(f"PI_LEFT_JET_H_{exponent}_END")

        # The source left packet does not make the four scalar reductions
        # exact as polynomial identities.  It retains their first h-adic
        # witnesses m1, tau1, g1, and k1.  Include those witnesses before
        # reading the h^97 coefficient; omitting them gives a valuewise but
        # source-invalid second jet.
        m1, tau1, g1, k1 = sp.symbols("m1 tau1 g1 k1")
        a_retained = a_solve + h * g1 / 2560
        b_retained = b_solve + h * (k1 - 32 * g1 * t0) / 131072
        retained_left_jet = sp.Poly(
            sp.expand(
                left_jet.as_expr().subs(
                    {
                        s1: s_solve + h * m1 / 32,
                        w1: w_solve + h * tau1 / 128,
                        a4: a_retained,
                        b5: b_retained,
                    }
                )
            ),
            h,
        )
        retained_head96 = sp.expand(retained_left_jet.coeff_monomial(h**96))
        if sp.expand(retained_head96 - reduced_left_head) != 0:
            raise RuntimeError("retained witnesses changed the h^96 head")
        retained_head97 = sp.expand(retained_left_jet.coeff_monomial(h**97))
        retained_head97_polynomial = sp.Poly(
            retained_head97,
            t0, v1, u1, b62, m1, tau1, g1, k1, lam,
            domain=sp.QQ,
        )
        print(
            "PI_LEFT_RETAINED_H97 "
            f"TERMS={len(retained_head97_polynomial.terms())} "
            f"TOTAL_DEGREE={retained_head97_polynomial.total_degree()}"
        )

        # These are exactly the root-value laws carried by
        # bridgeNuLeftPacket810 for the four retained witnesses.
        m1_solve = -9 * lam * t0
        tau1_solve = -(9 * lam * t0**2 + 144 * lam * v1) / 4
        g1_solve = -3 * lam * (7 * t0**3 - 48 * t0 * v1 - 384 * u1) / 2
        k1_solve = -9 * lam * (
            4096 * a_solve + 91 * t0**4 - 608 * t0**2 * v1
            - 2560 * t0 * u1 + 256 * v1**2
        )
        retained_head97_at_root = sp.cancel(
            retained_head97.subs(
                {
                    m1: m1_solve,
                    tau1: tau1_solve,
                    g1: g1_solve,
                    k1: k1_solve,
                }
            )
        )
        retained_head97_root_polynomial = sp.Poly(
            retained_head97_at_root,
            t0, v1, u1, b62, a3, b4, lam,
            domain=sp.QQ,
        )
        retained_head97_scale, retained_head97_integer = (
            retained_head97_root_polynomial.clear_denoms(convert=True)
        )
        print(
            "PI_LEFT_RETAINED_H97_ROOT "
            f"TERMS={len(retained_head97_integer.terms())} "
            f"SCALE={retained_head97_scale} "
            f"TOTAL_DEGREE={retained_head97_integer.total_degree()} "
            f"FRESH={','.join(sorted(str(variable) for variable in retained_head97_at_root.free_symbols - top_variables)) or '-'}"
        )
        if os.environ.get("EMIT_RETAINED_JET_EXPRESSIONS") == "1":
            print("PI_LEFT_RETAINED_H97_ROOT_BEGIN")
            print(sp.factor(retained_head97_at_root))
            print("PI_LEFT_RETAINED_H97_ROOT_END")

    bridge_specs = (
        (
            "mu",
            ROOT / "Fable810ScaleTwoTerminalIntegralBridgeScratch.lean",
            "bridgeMuLeftResidual810",
        ),
        (
            "nu",
            ROOT / "Fable810ScaleTwoNuIntegralBridgeScratch.lean",
            "bridgeNuLeftResidual810",
        ),
        (
            "xi",
            ROOT / "Fable810ScaleTwoNextIntegralBridgeScratch.lean",
            "bridgeXiLeftResidual810",
        ),
    )
    bridge_symbols = {
        symbol.name: symbol for symbol in (t0, v1, u1, b62)
    }
    bridge_residuals: dict[str, sp.Expr] = {}
    for label, path, name in bridge_specs:
        residual, residual_terms = parse_literal_definition(
            path, name, "R", bridge_symbols
        )
        bridge_residuals[label] = residual
        print(
            f"BRIDGE_{label.upper()}_SHA256={sha256(path.read_bytes()).hexdigest()} "
            f"TERMS={residual_terms}"
        )
    generators = (t0, v1, u1, b62)
    if os.environ.get("EMIT_JET_PROFILE") == "1":
        retained_head97_without_lambda = sp.cancel(retained_head97_at_root / lam)
        if lam in retained_head97_without_lambda.free_symbols:
            raise RuntimeError("lambda did not factor from the retained h^97 head")
        retained_head97_without_lambda = sp.Poly(
            retained_head97_without_lambda, *generators, domain=sp.QQ
        ).as_expr()
        left_ideal_generators = (
            bridge_residuals["mu"],
            bridge_residuals["nu"],
            bridge_residuals["xi"],
            reduced_left_polynomial.as_expr(),
        )
        left_quotients, left_remainder = sp.reduced(
            retained_head97_without_lambda,
            left_ideal_generators,
            *generators,
            domain=sp.QQ,
        )
        left_remainder_polynomial = sp.Poly(
            left_remainder, *generators, domain=sp.QQ
        )
        print(
            "PI_LEFT_RETAINED_H97_SEQUENTIAL_REDUCTION "
            f"QUOTIENT_TERMS={','.join(str(len(sp.Poly(q, *generators).terms())) for q in left_quotients)} "
            f"REMAINDER_TERMS={len(left_remainder_polynomial.terms())} "
            f"REMAINDER_TOTAL_DEGREE={left_remainder_polynomial.total_degree()}"
        )
        if os.environ.get("COMPUTE_LEFT_IDEAL") == "1":
            left_basis = sp.groebner(
                left_ideal_generators, *generators, order="grevlex", domain=sp.QQ
            )
            _left_groebner_quotients, left_groebner_remainder = (
                left_basis.reduce(retained_head97_without_lambda)
            )
            left_groebner_remainder_polynomial = sp.Poly(
                left_groebner_remainder, *generators, domain=sp.QQ
            )
            print(
                "PI_LEFT_RETAINED_H97_GROEBNER "
                f"BASIS_TERMS={','.join(str(len(sp.Poly(g, *generators).terms())) for g in left_basis.polys)} "
                f"REMAINDER_TERMS={len(left_groebner_remainder_polynomial.terms())} "
                f"REMAINDER_TOTAL_DEGREE={left_groebner_remainder_polynomial.total_degree()}"
            )
            if os.environ.get("EMIT_RETAINED_JET_EXPRESSIONS") == "1":
                print("PI_LEFT_RETAINED_H97_GROEBNER_REMAINDER_BEGIN")
                print(sp.factor(left_groebner_remainder))
                print("PI_LEFT_RETAINED_H97_GROEBNER_REMAINDER_END")
    for label, divisor_labels in (
        ("MU_NU_XI", ("mu", "nu", "xi")),
        ("XI_NU_MU", ("xi", "nu", "mu")),
        ("NU_XI_MU", ("nu", "xi", "mu")),
    ):
        quotients, remainder = sp.reduced(
            reduced_left_polynomial.as_expr(),
            tuple(bridge_residuals[name] for name in divisor_labels),
            *generators,
            domain=sp.QQ,
        )
        remainder_polynomial = sp.Poly(
            remainder, *generators, domain=sp.QQ
        )
        print(
            f"PI_LEFT_REDUCTION={label} QUOTIENT_TERMS="
            f"{','.join(str(len(sp.Poly(q, *generators).terms())) for q in quotients)} "
            f"REMAINDER_TERMS={len(remainder_polynomial.terms())} "
            f"REMAINDER_TOTAL_DEGREE={remainder_polynomial.total_degree()}"
        )
        if os.environ.get("EMIT_REMAINDERS") == "1":
            print(f"PI_LEFT_REMAINDER_{label}_BEGIN")
            print(sp.factor(remainder_polynomial.as_expr()))
            print(f"PI_LEFT_REMAINDER_{label}_END")
    if os.environ.get("EMIT_CLEARING") == "1":
        print("PI_CLEARING_BEGIN")
        print(cleared_pi_numerator)
        print("PI_CLEARING_END")
    if os.environ.get("EMIT_CLEARING_HEAD") == "1":
        print("PI_LEFT_HEAD_BEGIN")
        print(sp.factor(left_head))
        print("PI_LEFT_HEAD_END")
