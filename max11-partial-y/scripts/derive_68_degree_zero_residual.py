#!/usr/bin/env python3
"""Derive the (6,8) weight-11 first integral and weight-13 degree-zero primitive.

Puiseux/Faber expansion g = Σ c_i f^{i/6} down to i = -5, compared with the
committed firstIntegralFour68 / firstIntegralThree68, then the unused row h2
is made exact and the degree-zero row U dE - D dV is integrated.  Groups and
the weighted-homogeneous certificate are emitted for
Grok68ScaleTwoDegreeZeroPrimitiveScratch.lean.

Modelled on scripts/derive_68_small_gap_residual.py (runner contract) and
derive_610_degree_zero_residual.py (Faber + closed one-form + residual groups).

Run:
  JC2_JOB_TAG=68-degree-zero EMIT_GROUPS=1 EMIT_CERTIFICATES=1 \\
    ./scripts/max11_cas_run.py --name 68-degree-zero --timeout 1800 -- \\
    python3 scripts/derive_68_degree_zero_residual.py
"""

from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import math
import os
import platform
import socket
import time

import sympy as sp


job_tag = os.environ.get("JC2_JOB_TAG", "")
if platform.system() != "Linux":
    raise SystemExit("refusing non-Linux CAS run")
if not job_tag:
    raise SystemExit("JC2_JOB_TAG is required")
print(f"host={socket.gethostname()} job_tag={job_tag}", flush=True)

ROOT = Path(__file__).resolve().parent.parent
started = time.monotonic()


def checkpoint(label: str) -> None:
    print(f"{label}_SECONDS={time.monotonic() - started:.3f}", flush=True)


L, A, B, C0, D, E = sp.symbols("L A B C0 D E")
P, Q, R, S, T, U, V = sp.symbols("P Q R S T U V")
alpha, beta, gamma, delta, epsilon, zeta, eta = sp.symbols(
    "alpha beta gamma delta epsilon zeta eta"
)
ca, cb, cg, cd, ce, cz, cet = sp.symbols("ca cb cg cd ce cz cet")
constant_residuals = (ca, cb, cg, cd, ce, cz, cet)
dynamic = (A, B, C0, D, E)
base_symbols = (L, A, B, C0, D, E, P, Q, R, S, T, U, V)

weights = {
    L: 1, A: 2, B: 3, C0: 4, D: 5, E: 6,
    P: 2, Q: 3, R: 4, S: 5, T: 6, U: 7, V: 8,
    ca: 2, cb: 3, cg: 4, cd: 5, ce: 6, cz: 7, cet: 8,
    alpha: 2, beta: 3, gamma: 4, delta: 5, epsilon: 6, zeta: 7, eta: 8,
}


def monomials_of_weight(target: int, generators: tuple[sp.Symbol, ...]) -> tuple[sp.Expr, ...]:
    output: list[sp.Expr] = []

    def visit(index: int, remaining: int, current: sp.Expr) -> None:
        if remaining == 0:
            output.append(current)
            return
        if index == len(generators):
            return
        variable = generators[index]
        weight = weights[variable]
        for power in range(remaining // weight + 1):
            visit(index + 1, remaining - power * weight, current * variable**power)

    visit(0, target, sp.Integer(1))
    return tuple(output)


def weighted_degree(expr: sp.Expr, gens: tuple[sp.Symbol, ...] | None = None) -> set[int]:
    if expr == 0:
        return {0}
    gens = gens if gens is not None else tuple(expr.free_symbols)
    present = [symbol for symbol in gens if symbol in expr.free_symbols]
    if not present:
        return {0}
    polynomial = sp.Poly(sp.expand(expr), *present, domain=sp.QQ)
    return {
        sum(weights[symbol] * exponent for symbol, exponent in zip(present, monomial))
        for monomial, coefficient in polynomial.terms()
        if coefficient != 0
    }


def qq_lcm(values: list[sp.Rational]) -> int:
    denoms = [int(sp.Integer(sp.Rational(value).q)) for value in values if value != 0]
    if not denoms:
        return 1
    return int(math.lcm(*denoms))


def content_and_scale(expr: sp.Expr, gens: tuple[sp.Symbol, ...]) -> tuple[sp.Expr, int, int]:
    polynomial = sp.Poly(sp.expand(expr), *gens, domain=sp.QQ)
    if polynomial.is_zero:
        return sp.Integer(0), 1, 1
    scale = qq_lcm([sp.Rational(coefficient) for coefficient in polynomial.coeffs()])
    cleared = sp.Poly(sp.expand(scale * polynomial.as_expr()), *gens, domain=sp.ZZ)
    return cleared.as_expr(), scale, int(cleared.content())


def lean_fraction(expr: sp.Expr, gens: tuple[sp.Symbol, ...], indent: str = "  ") -> str:
    """Emit a Lean field polynomial, factored as (integer poly) / denom when possible."""

    expanded = sp.expand(expr)
    if expanded == 0:
        return f"{indent}0"
    factored = sp.factor(expanded)
    numerator, denominator = sp.fraction(sp.together(factored))
    numerator = sp.expand(numerator)
    denominator = sp.expand(denominator)
    if denominator == 1:
        body = lean_sum(numerator, gens, indent)
        return body
    if denominator < 0:
        numerator = sp.expand(-numerator)
        denominator = -denominator
    body = lean_sum(numerator, gens, indent + "  ")
    den_text = str(int(denominator)) if denominator == int(denominator) else str(denominator)
    return f"{indent}(\n{body}\n{indent}) / {den_text}"


def lean_sum(expr: sp.Expr, gens: tuple[sp.Symbol, ...], indent: str) -> str:
    present = [symbol for symbol in gens if symbol in sp.expand(expr).free_symbols]
    if not present:
        value = sp.QQ(expr)
        return f"{indent}({value})"
    polynomial = sp.Poly(sp.expand(expr), *present, domain=sp.QQ)
    lines: list[str] = []
    for position, (monomial, coefficient) in enumerate(polynomial.terms()):
        coeff = sp.Rational(coefficient)
        negative = coeff < 0
        absolute = -coeff if negative else coeff
        factors: list[str] = []
        if absolute != 1 or not any(monomial):
            if absolute.q == 1:
                factors.append(f"({int(absolute)} : F)")
            else:
                factors.append(f"({int(absolute.p)} / {int(absolute.q)} : F)")
        for symbol, exponent in zip(present, monomial):
            if exponent == 1:
                factors.append(str(symbol))
            elif exponent:
                factors.append(f"{symbol} ^ {exponent}")
        term = " * ".join(factors) if factors else "(1 : F)"
        if position == 0:
            prefix = f"{indent}- " if negative else f"{indent}"
        else:
            prefix = f"{indent}- " if negative else f"{indent}+ "
        lines.append(prefix + term)
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Integrated octic coefficients and committed first integrals (from Lean)
# ---------------------------------------------------------------------------

def integrated_P(A_, alpha_):
    return sp.Rational(4, 3) * A_ + alpha_


def integrated_Q(L_, A_, B_, beta_):
    return sp.Rational(4, 3) * B_ + sp.Rational(7, 6) * L_ * A_ + beta_


def integrated_R(L_, A_, B_, C0_, alpha_, gamma_):
    return (
        sp.Rational(4, 3) * C0_
        + sp.Rational(2, 9) * A_ ** 2
        + sp.Rational(7, 6) * L_ * B_
        + alpha_ * A_
        + gamma_
    )


def integrated_S(L_, A_, B_, C0_, D_, alpha_, beta_, delta_):
    return (
        sp.Rational(4, 3) * D_
        + sp.Rational(4, 9) * A_ * B_
        + L_ * (sp.Rational(7, 6) * C0_ + sp.Rational(7, 72) * A_ ** 2)
        + alpha_ * B_
        + sp.Rational(5, 6) * beta_ * A_
        + delta_
    )


def integrated_T(L_, A_, B_, C0_, D_, E_, alpha_, beta_, gamma_, epsilon_):
    return (
        sp.Rational(4, 3) * E_
        + sp.Rational(2, 9) * B_ ** 2
        + sp.Rational(4, 9) * A_ * C0_
        - sp.Rational(4, 81) * A_ ** 3
        + L_ * (sp.Rational(7, 6) * D_ + sp.Rational(7, 36) * A_ * B_)
        + alpha_ * C0_
        + sp.Rational(5, 6) * beta_ * B_
        + sp.Rational(2, 3) * gamma_ * A_
        + epsilon_
    )


def integrated_U(L_, A_, B_, C0_, D_, E_, alpha_, beta_, gamma_, delta_, zeta_):
    return (
        sp.Rational(4, 9) * B_ * C0_
        + sp.Rational(4, 9) * A_ * D_
        - sp.Rational(4, 27) * A_ ** 2 * B_
        + L_
        * (
            sp.Rational(7, 6) * E_
            + sp.Rational(7, 72) * B_ ** 2
            + sp.Rational(7, 36) * A_ * C0_
            - sp.Rational(35, 1296) * A_ ** 3
        )
        + alpha_ * D_
        + beta_ * (sp.Rational(5, 6) * C0_ - sp.Rational(5, 72) * A_ ** 2)
        + sp.Rational(2, 3) * gamma_ * B_
        + sp.Rational(1, 2) * delta_ * A_
        + zeta_
    )


def integrated_V(
    L_, A_, B_, C0_, D_, E_, alpha_, beta_, gamma_, delta_, epsilon_, eta_
):
    return (
        sp.Rational(2, 9) * C0_ ** 2
        + sp.Rational(4, 9) * B_ * D_
        + sp.Rational(4, 9) * A_ * E_
        - sp.Rational(4, 27) * A_ * B_ ** 2
        - sp.Rational(4, 27) * A_ ** 2 * C0_
        + sp.Rational(5, 243) * A_ ** 4
        + L_
        * (
            sp.Rational(7, 36) * B_ * C0_
            + sp.Rational(7, 36) * A_ * D_
            - sp.Rational(35, 432) * A_ ** 2 * B_
        )
        + alpha_ * E_
        + beta_ * (sp.Rational(5, 6) * D_ - sp.Rational(5, 36) * A_ * B_)
        + gamma_ * (sp.Rational(2, 3) * C0_ - sp.Rational(1, 9) * A_ ** 2)
        + sp.Rational(1, 2) * delta_ * B_
        + sp.Rational(1, 3) * epsilon_ * A_
        + eta_
    )


def first_integral_four(L_, A_, B_, C0_, D_, E_, beta_, gamma_, delta_, epsilon_, zeta_):
    return (
        -sp.Rational(8, 27) * B_ ** 3
        + A_ * zeta_
        + 2 * B_ * epsilon_
        + 3 * C0_ * delta_
        + 4 * D_ * gamma_
        + 5 * E_ * beta_
        - sp.Rational(8, 9) * A_ ** 2 * D_
        - sp.Rational(5, 12) * B_ ** 2 * beta_
        - sp.Rational(3, 4) * A_ ** 2 * delta_
        + sp.Rational(7, 12) * C0_ ** 2 * L_
        + sp.Rational(8, 3) * B_ * E_
        + sp.Rational(8, 3) * C0_ * D_
        + sp.Rational(35, 216) * A_ ** 3 * beta_
        + sp.Rational(40, 81) * A_ ** 3 * B_
        + sp.Rational(385, 5184) * A_ ** 4 * L_
        - sp.Rational(35, 72) * A_ * B_ ** 2 * L_
        - sp.Rational(35, 72) * A_ ** 2 * C0_ * L_
        - sp.Rational(16, 9) * A_ * B_ * C0_
        - sp.Rational(5, 6) * A_ * C0_ * beta_
        - sp.Rational(4, 3) * A_ * B_ * gamma_
        + sp.Rational(7, 6) * A_ * E_ * L_
        + sp.Rational(7, 6) * B_ * D_ * L_
    )


def first_integral_three(L_, A_, B_, C0_, D_, E_, beta_, gamma_, delta_, epsilon_, zeta_):
    return (
        -sp.Rational(16, 243) * A_ ** 5
        + sp.Rational(4, 3) * D_ ** 2
        + B_ * zeta_
        + 2 * C0_ * epsilon_
        + 3 * D_ * delta_
        + 4 * E_ * gamma_
        - sp.Rational(35, 216) * B_ ** 3 * L_
        - sp.Rational(8, 9) * A_ * C0_ ** 2
        - sp.Rational(8, 9) * B_ ** 2 * C0_
        - sp.Rational(8, 9) * A_ ** 2 * E_
        - sp.Rational(2, 3) * A_ ** 2 * epsilon_
        - sp.Rational(2, 3) * B_ ** 2 * gamma_
        + sp.Rational(8, 3) * C0_ * E_
        + sp.Rational(8, 27) * A_ ** 3 * gamma_
        + sp.Rational(20, 27) * A_ ** 2 * B_ ** 2
        + sp.Rational(40, 81) * A_ ** 3 * C0_
        - sp.Rational(35, 72) * A_ ** 2 * D_ * L_
        - sp.Rational(16, 9) * A_ * B_ * D_
        - sp.Rational(5, 6) * A_ * D_ * beta_
        - sp.Rational(5, 6) * B_ * C0_ * beta_
        - sp.Rational(4, 3) * A_ * C0_ * gamma_
        - sp.Rational(3, 2) * A_ * B_ * delta_
        + sp.Rational(7, 6) * B_ * E_ * L_
        + sp.Rational(7, 6) * C0_ * D_ * L_
        + sp.Rational(35, 72) * A_ ** 2 * B_ * beta_
        + sp.Rational(385, 1296) * A_ ** 3 * B_ * L_
        - sp.Rational(35, 36) * A_ * B_ * C0_ * L_
    )


# ---------------------------------------------------------------------------
# Faber / Puiseux g = Σ c_i f^{i/6}
# ---------------------------------------------------------------------------

tt = sp.symbols("t")
uu = A * tt**2 + B * tt**3 + C0 * tt**4 + D * tt**5 + E * tt**6
faber_basis = (
    (8, sp.Rational(4, 3), 1),
    (7, sp.Rational(7, 6), L),
    (6, sp.Integer(1), alpha),
    (5, sp.Rational(5, 6), beta),
    (4, sp.Rational(2, 3), gamma),
    (3, sp.Rational(1, 2), delta),
    (2, sp.Rational(1, 3), epsilon),
    (1, sp.Rational(1, 6), zeta),
    (0, sp.Integer(0), eta),
)


def binomial_series(power: sp.Expr, degree: int) -> sp.Expr:
    return sp.expand(
        sum(sp.binomial(power, exponent) * uu**exponent for exponent in range(degree // 2 + 1))
    )


def coefficient_y(degree: int) -> sp.Expr:
    answer = 0
    for leading_degree, power, scalar in faber_basis:
        target = leading_degree - degree
        if target < 0:
            continue
        answer += scalar * binomial_series(power, target).coeff(tt, target)
    return sp.expand(answer)


def coefficient_below_zero(depth: int) -> sp.Expr:
    answer = 0
    for leading_degree, power, scalar in faber_basis:
        target = leading_degree + depth
        answer += scalar * binomial_series(power, target).coeff(tt, target)
    return sp.expand(answer)


print("FABER_POLYNOMIAL_PART")
# coefficient_y(k) is the z^k coefficient of the octic, i.e. t^{8-k} of g/z^8.
for degree, name in (
    (6, "P"),
    (5, "Q"),
    (4, "R"),
    (3, "S"),
    (2, "T"),
    (1, "U"),
    (0, "V"),
):
    coeff = coefficient_y(degree)
    print(f"FABER_Y_{degree}_{name}_WEIGHTS={sorted(weighted_degree(coeff))}")
    print(f"FABER_Y_{degree}_{name}_TERMS={len(sp.Add.make_args(coeff))}")

P_faber = coefficient_y(6)
Q_faber = coefficient_y(5)
R_faber = coefficient_y(4)
S_faber = coefficient_y(3)
T_faber = coefficient_y(2)
U_faber = coefficient_y(1)
V_faber = coefficient_y(0)
assert sp.expand(P_faber - integrated_P(A, alpha)) == 0
assert sp.expand(Q_faber - integrated_Q(L, A, B, beta)) == 0
assert sp.expand(R_faber - integrated_R(L, A, B, C0, alpha, gamma)) == 0
assert sp.expand(S_faber - integrated_S(L, A, B, C0, D, alpha, beta, delta)) == 0
assert sp.expand(T_faber - integrated_T(L, A, B, C0, D, E, alpha, beta, gamma, epsilon)) == 0
assert sp.expand(U_faber - integrated_U(L, A, B, C0, D, E, alpha, beta, gamma, delta, zeta)) == 0
assert (
    sp.expand(
        V_faber
        - integrated_V(L, A, B, C0, D, E, alpha, beta, gamma, delta, epsilon, eta)
    )
    == 0
)
print("FABER_MATCHES_INTEGRATED_PQRSTUV=1")
checkpoint("FABER_POLYNOMIAL")

c_m1 = coefficient_below_zero(1)
c_m2 = coefficient_below_zero(2)
c_m3 = coefficient_below_zero(3)
c_m4 = coefficient_below_zero(4)
c_m5 = coefficient_below_zero(5)
print(f"FABER_C_MINUS_1_WEIGHTS={sorted(weighted_degree(c_m1))}")
print(f"FABER_C_MINUS_2_WEIGHTS={sorted(weighted_degree(c_m2))}")
print(f"FABER_C_MINUS_3_WEIGHTS={sorted(weighted_degree(c_m3))}")
print(f"FABER_C_MINUS_4_WEIGHTS={sorted(weighted_degree(c_m4))}")
print(f"FABER_C_MINUS_5_WEIGHTS={sorted(weighted_degree(c_m5))}")
print(
    "FABER_C_TERMS="
    + ",".join(
        str(len(sp.Add.make_args(expr)))
        for expr in (c_m1, c_m2, c_m3, c_m4, c_m5)
    )
)
checkpoint("FABER_NEGATIVE")

I4 = sp.expand(first_integral_four(L, A, B, C0, D, E, beta, gamma, delta, epsilon, zeta))
I3 = sp.expand(first_integral_three(L, A, B, C0, D, E, beta, gamma, delta, epsilon, zeta))
print(f"I4_WEIGHTS={sorted(weighted_degree(I4))}")
print(f"I3_WEIGHTS={sorted(weighted_degree(I3))}")

# Compare Faber tails with the committed first integrals.  A constant rational
# scale is allowed; the Jacobian row is 6 * d(c_i) up to the f_z leading term.
ratio_candidates = (
    sp.Integer(1),
    sp.Integer(6),
    sp.Integer(-6),
    sp.Integer(2),
    sp.Integer(-2),
    sp.Rational(1, 6),
    sp.Rational(-1, 6),
)
i4_scale = None
i3_scale = None
for scale in ratio_candidates:
    if sp.expand(I4 - scale * c_m1) == 0:
        i4_scale = scale
    if sp.expand(I3 - scale * c_m2) == 0:
        i3_scale = scale
print(f"I4_FABER_SCALE={i4_scale}")
print(f"I3_FABER_SCALE={i3_scale}")
if i4_scale is None:
    remainder = sp.expand(I4)
    # Try a linear combination with lower Faber directions of matching weight.
    print("I4_NOT_PURE_FABER_C_MINUS_1")
    print(f"I4_MINUS_C_MINUS_1_TERMS={len(sp.Add.make_args(sp.expand(I4 - c_m1)))}")
if i3_scale is None:
    print("I3_NOT_PURE_FABER_C_MINUS_2")
    print(f"I3_MINUS_C_MINUS_2_TERMS={len(sp.Add.make_args(sp.expand(I3 - c_m2)))}")
checkpoint("MATCHED_I4_I3")


# ---------------------------------------------------------------------------
# Integrated locus in residual constants
# ---------------------------------------------------------------------------

residual_map = {
    alpha: ca,
    beta: cb,
    gamma: cg,
    delta: cd,
    epsilon: ce,
    zeta: cz,
    eta: cet,
}

Pv = sp.expand(integrated_P(A, ca))
Qv = sp.expand(integrated_Q(L, A, B, cb))
Rv = sp.expand(integrated_R(L, A, B, C0, ca, cg))
Sv = sp.expand(integrated_S(L, A, B, C0, D, ca, cb, cd))
Tv = sp.expand(integrated_T(L, A, B, C0, D, E, ca, cb, cg, ce))
Uv = sp.expand(integrated_U(L, A, B, C0, D, E, ca, cb, cg, cd, cz))
Vv = sp.expand(integrated_V(L, A, B, C0, D, E, ca, cb, cg, cd, ce, cet))
I4v = sp.expand(first_integral_four(L, A, B, C0, D, E, cb, cg, cd, ce, cz))
I3v = sp.expand(first_integral_three(L, A, B, C0, D, E, cb, cg, cd, ce, cz))
c_m1v = sp.expand(c_m1.subs(residual_map))
c_m2v = sp.expand(c_m2.subs(residual_map))
c_m3v = sp.expand(c_m3.subs(residual_map))
c_m4v = sp.expand(c_m4.subs(residual_map))
c_m5v = sp.expand(c_m5.subs(residual_map))


def gradient(expression: sp.Expr) -> list[sp.Expr]:
    return [sp.expand(sp.diff(expression, variable)) for variable in dynamic]


def close_and_integrate(
    omega: list[sp.Expr],
    invariants: list[tuple[str, sp.Expr, int]],
    label: str,
) -> tuple[sp.Expr, dict[str, sp.Expr], int]:
    """Add weighted multipliers of d(invariants) so omega becomes closed, then integrate."""

    generators = (L, *dynamic, *constant_residuals)
    unknowns: list[sp.Symbol] = []
    multipliers: list[tuple[str, sp.Expr]] = []
    corrected = list(omega)
    for name, invariant, extra_weight in invariants:
        monomials = monomials_of_weight(extra_weight, generators)
        coefficients = sp.symbols(f"m_{label}_{name}_0:{len(monomials)}")
        unknowns.extend(coefficients)
        multiplier = sp.Add(
            *(coefficient * monomial for coefficient, monomial in zip(coefficients, monomials))
        )
        multipliers.append((name, multiplier))
        inv_grad = gradient(invariant)
        for index in range(len(dynamic)):
            corrected[index] += multiplier * inv_grad[index]
    corrected = [sp.expand(component) for component in corrected]
    checkpoint(f"{label}_CORRECTED_FORM")

    closure_coefficients: list[sp.Expr] = []
    for i, variable_i in enumerate(dynamic):
        for j in range(i):
            closure = sp.expand(
                sp.diff(corrected[i], dynamic[j]) - sp.diff(corrected[j], variable_i)
            )
            if closure == 0:
                continue
            closure_coefficients.extend(sp.Poly(closure, *generators).coeffs())
    checkpoint(f"{label}_CLOSURE_COEFFICIENTS")
    print(f"{label}_CLOSURE_EQUATIONS={len(closure_coefficients)}")
    print(
        f"{label}_MULTIPLIER_BASE_SIZES="
        + ",".join(str(len(monomials_of_weight(extra, generators))) for _n, _i, extra in invariants)
    )
    matrix_rows = 0
    if not unknowns:
        if any(coeff != 0 for coeff in closure_coefficients):
            raise RuntimeError(f"{label}: uncorrected form is not closed")
        solution = {}
        print(f"{label}_FREE_PARAMETERS=0")
    elif not closure_coefficients:
        solution = {unknown: sp.Integer(0) for unknown in unknowns}
        print(f"{label}_CLOSURE_MATRIX=0x{len(unknowns)}")
        print(f"{label}_FREE_PARAMETERS={len(unknowns)}")
    else:
        matrix, rhs = sp.linear_eq_to_matrix(closure_coefficients, unknowns)
        matrix_rows = matrix.rows
        checkpoint(f"{label}_CLOSURE_MATRIX")
        print(f"{label}_CLOSURE_MATRIX={matrix.rows}x{matrix.cols}")
        solutions = list(sp.linsolve((matrix, rhs), unknowns))
        if len(solutions) != 1:
            raise RuntimeError(
                f"{label}: expected one affine solution family, got {len(solutions)}"
            )
        solution_tuple = solutions[0]
        free = set().union(*(entry.free_symbols for entry in solution_tuple)) & set(unknowns)
        print(f"{label}_FREE_PARAMETERS={len(free)}")
        solution = {
            unknown: sp.expand(value.subs({symbol: 0 for symbol in free}))
            for unknown, value in zip(unknowns, solution_tuple)
        }
        corrected = [sp.expand(component.subs(solution)) for component in corrected]
    checkpoint(f"{label}_CLOSURE_SOLVED")

    solved_multipliers = {
        name: sp.expand(multiplier.subs(solution)) for name, multiplier in multipliers
    }
    for name, value in solved_multipliers.items():
        print(f"{label}_CORRECTION_{name.upper()}={sp.factor(value)}")

    integral = sp.Integer(0)
    for variable, component in zip(dynamic, corrected):
        remainder = sp.expand(component - sp.diff(integral, variable))
        integral = sp.expand(integral + sp.integrate(remainder, variable))
    if any(
        sp.expand(sp.diff(integral, variable) - component) != 0
        for variable, component in zip(dynamic, corrected)
    ):
        raise RuntimeError(f"{label}: integrated one-form does not reproduce the closed form")
    print(
        f"{label}_INTEGRAL_WEIGHTS={sorted(weighted_degree(integral, generators))}"
    )
    print(f"{label}_INTEGRAL_TERMS={len(sp.Poly(integral, *generators).terms())}")
    checkpoint(f"{label}_INTEGRATED")
    return integral, solved_multipliers, matrix_rows


def jacobian_row_components(
    ambient: dict[str, sp.Expr],
    formula,
) -> list[sp.Expr]:
    """formula(dA,dB,dC0,dD,dE, dR,dS,dT,dU,dV) -> components on the integrated locus."""

    dA, dB, dC0, dD, dE = sp.symbols("dA dB dC0 dD dE")
    dR, dS, dT, dU, dV = sp.symbols("dR dS dT dU dV")
    raw = formula(dA, dB, dC0, dD, dE, dR, dS, dT, dU, dV)
    # Substitute total differentials of integrated coefficients.
    replacements = {
        dR: sum(sp.diff(ambient["R"], var) * dvar for var, dvar in zip(dynamic, (dA, dB, dC0, dD, dE))),
        dS: sum(sp.diff(ambient["S"], var) * dvar for var, dvar in zip(dynamic, (dA, dB, dC0, dD, dE))),
        dT: sum(sp.diff(ambient["T"], var) * dvar for var, dvar in zip(dynamic, (dA, dB, dC0, dD, dE))),
        dU: sum(sp.diff(ambient["U"], var) * dvar for var, dvar in zip(dynamic, (dA, dB, dC0, dD, dE))),
        dV: sum(sp.diff(ambient["V"], var) * dvar for var, dvar in zip(dynamic, (dA, dB, dC0, dD, dE))),
    }
    restricted = sp.expand(raw.subs(replacements))
    return [
        sp.expand(restricted.coeff(dvar))
        for dvar in (dA, dB, dC0, dD, dE)
    ]


ambient = {"R": Rv, "S": Sv, "T": Tv, "U": Uv, "V": Vv, "Q": Qv}

# h4: U dA + 2 T dB + 3 S dC0 + 4 R dD + 5 Q dE - 4 A dU - 3 B dT - 2 C0 dS - D dR
row4 = jacobian_row_components(
    ambient,
    lambda dA, dB, dC0, dD, dE, dR, dS, dT, dU, dV: (
        Uv * dA
        + 2 * Tv * dB
        + 3 * Sv * dC0
        + 4 * Rv * dD
        + 5 * Qv * dE
        - 4 * A * dU
        - 3 * B * dT
        - 2 * C0 * dS
        - D * dR
    ),
)
# h3: U dB + 2 T dC0 + 3 S dD + 4 R dE - 4 A dV - 3 B dU - 2 C0 dT - D dS
row3 = jacobian_row_components(
    ambient,
    lambda dA, dB, dC0, dD, dE, dR, dS, dT, dU, dV: (
        Uv * dB
        + 2 * Tv * dC0
        + 3 * Sv * dD
        + 4 * Rv * dE
        - 4 * A * dV
        - 3 * B * dU
        - 2 * C0 * dT
        - D * dS
    ),
)
# h2: U dC0 + 2 T dD + 3 S dE - 3 B dV - 2 C0 dU - D dT
row2 = jacobian_row_components(
    ambient,
    lambda dA, dB, dC0, dD, dE, dR, dS, dT, dU, dV: (
        Uv * dC0
        + 2 * Tv * dD
        + 3 * Sv * dE
        - 3 * B * dV
        - 2 * C0 * dU
        - D * dT
    ),
)
# h1: U dD + 2 T dE - 2 C0 dV - D dU
row1 = jacobian_row_components(
    ambient,
    lambda dA, dB, dC0, dD, dE, dR, dS, dT, dU, dV: (
        Uv * dD + 2 * Tv * dE - 2 * C0 * dV - D * dU
    ),
)
# h0: U dE - D dV
row0 = jacobian_row_components(
    ambient,
    lambda dA, dB, dC0, dD, dE, dR, dS, dT, dU, dV: Uv * dE - D * dV,
)

# Sanity: d(I4) equals row4, d(I3) equals row3 on the integrated locus.
grad_I4 = gradient(I4v)
grad_I3 = gradient(I3v)
if any(sp.expand(left - right) != 0 for left, right in zip(grad_I4, row4)):
    raise RuntimeError("d(firstIntegralFour68) does not match integrated row h4")
if any(sp.expand(left - right) != 0 for left, right in zip(grad_I3, row3)):
    raise RuntimeError("d(firstIntegralThree68) does not match integrated row h3")
print("I4_I3_MATCH_ROWS_H4_H3=1")
checkpoint("ROW_SANITY")

# Close row h2 using I4 (weight 9, extra 2) and I3 (weight 10, extra 1).
# Row h1 has weight 12, so it cannot mix into this weight-11 form with a
# polynomial multiplier; the plan fallback is to take Faber c_{-3} as I2.
used_row_h1 = False
try:
    I2_integral, I2_multipliers, _ = close_and_integrate(
        row2,
        [("I4", I4v, 2), ("I3", I3v, 1)],
        "ROW2",
    )
except RuntimeError as error:
    print(f"ROW2_CLOSE_FAILED={error}")
    print("ROW2_FALLBACK=FABER_C_MINUS_3")
    I2_integral = c_m3v
    I2_multipliers = {"I4": sp.Integer(0), "I3": sp.Integer(0)}
I2v = I2_integral
print(f"I2_WEIGHTS={sorted(weighted_degree(I2v))}")
# Compare with Faber c_{-3}.
i2_faber_scale = None
for scale in ratio_candidates:
    if sp.expand(I2v - scale * c_m3v) == 0:
        i2_faber_scale = scale
        break
print(f"I2_FABER_C_MINUS_3_SCALE={i2_faber_scale}")
if i2_faber_scale is None:
    # Allow a combination with I4, I3 of matching total weight 11.
    # I2 ?= a * c_m3 + p2 * I4 + p1 * I3 with p2 weight 2, p1 weight 1.
    print("I2_NOT_PURE_FABER; recording combination remainder against c_m3")
    print(
        f"I2_MINUS_C_MINUS_3_TERMS={len(sp.Poly(sp.expand(I2v - c_m3v), L, *dynamic, *constant_residuals).terms())}"
    )

# If row2 was not closable (close_and_integrate raises), we would retry with I1.
# Optional: also close row h1 to see whether I2 needed it.  The solved
# multipliers already record the exact combination with h4 and h3.

# Close the degree-zero row using I4, I3, I2.
rho_integral, rho_multipliers, _ = close_and_integrate(
    row0,
    [("I4", I4v, 4), ("I3", I3v, 3), ("I2", I2v, 2)],
    "ROW0",
)
print(f"RHO_WEIGHTS={sorted(weighted_degree(rho_integral))}")
rho_faber_scale = None
for scale in ratio_candidates:
    if sp.expand(rho_integral - scale * c_m5v) == 0:
        rho_faber_scale = scale
        break
print(f"RHO_FABER_C_MINUS_5_SCALE={rho_faber_scale}")
if rho_faber_scale is None:
    print(
        "RHO_MINUS_C_MINUS_5_TERMS="
        f"{len(sp.Poly(sp.expand(rho_integral - c_m5v), L, *dynamic, *constant_residuals).terms())}"
    )

# If I2 was not needed, the I2 multiplier is zero; record that.
print(f"ROW0_USED_I2={int(rho_multipliers['I2'] != 0)}")
print(f"ROW2_USED_I4={int(I2_multipliers['I4'] != 0)}")
print(f"ROW2_USED_I3={int(I2_multipliers['I3'] != 0)}")

# Homogeneity of the primitive on the residual locus.
if weighted_degree(rho_integral) != {13}:
    raise RuntimeError(f"primitive is not weight 13: {weighted_degree(rho_integral)}")
print("RHO_WEIGHT_13=1")

# Group by residual constants, then rewrite using I4, I3, I2 as opaque summands.
generators = (L, *dynamic, *constant_residuals)
if any(
    sp.degree(rho_integral, residual) > 1 for residual in constant_residuals
):
    raise RuntimeError("degree-zero residual is nonlinear in old residuals")

groups: dict[str, sp.Expr] = {}
constant_part = rho_integral
for residual_constant, name in zip(
    constant_residuals, ("ALPHA", "BETA", "GAMMA", "DELTA", "EPSILON", "ZETA", "ETA")
):
    coefficient = sp.expand(sp.diff(rho_integral, residual_constant))
    if any(other in coefficient.free_symbols for other in constant_residuals):
        raise RuntimeError("degree-zero residual is nonlinear in old residuals")
    groups[name] = coefficient
    constant_part -= residual_constant * coefficient
groups["BASE"] = sp.expand(constant_part)

# Attempt the plan grouping: rho = base + Σ residual*G + I4*G4 + I3*G3 + I2*G2
# with G4, G3, G2 residual-free.  Use the solved ROW0 multipliers as the
# candidate G4, G3, G2; the remainder is then grouped by residuals again.
candidate_four = rho_multipliers["I4"]
candidate_three = rho_multipliers["I3"]
candidate_two = rho_multipliers["I2"]
if any(symbol in candidate_four.free_symbols for symbol in constant_residuals):
    print("I4_GROUP_DEPENDS_ON_RESIDUALS=1")
else:
    print("I4_GROUP_DEPENDS_ON_RESIDUALS=0")
if any(symbol in candidate_three.free_symbols for symbol in constant_residuals):
    print("I3_GROUP_DEPENDS_ON_RESIDUALS=1")
else:
    print("I3_GROUP_DEPENDS_ON_RESIDUALS=0")
if any(symbol in candidate_two.free_symbols for symbol in constant_residuals):
    print("I2_GROUP_DEPENDS_ON_RESIDUALS=1")
else:
    print("I2_GROUP_DEPENDS_ON_RESIDUALS=0")

rewritten = sp.expand(
    rho_integral
    - candidate_four * I4v
    - candidate_three * I3v
    - candidate_two * I2v
)
print(
    f"REWRITE_REMAINDER_WEIGHTS={sorted(weighted_degree(rewritten))}"
)
print(
    f"REWRITE_REMAINDER_TERMS={len(sp.Poly(rewritten, *generators).terms())}"
)
rewrite_groups: dict[str, sp.Expr] = {}
rewrite_base = rewritten
for residual_constant, name in zip(
    constant_residuals, ("ALPHA", "BETA", "GAMMA", "DELTA", "EPSILON", "ZETA", "ETA")
):
    coefficient = sp.expand(sp.diff(rewritten, residual_constant))
    rewrite_groups[name] = coefficient
    rewrite_base -= residual_constant * coefficient
rewrite_groups["BASE"] = sp.expand(rewrite_base)
rewrite_groups["FOUR"] = candidate_four
rewrite_groups["THREE"] = candidate_three
rewrite_groups["TWO"] = candidate_two

# Check that the rewrite reconstructs rho.
reconstruction = rewrite_groups["BASE"]
for residual_constant, name in zip(
    constant_residuals, ("ALPHA", "BETA", "GAMMA", "DELTA", "EPSILON", "ZETA", "ETA")
):
    reconstruction += residual_constant * rewrite_groups[name]
reconstruction += (
    rewrite_groups["FOUR"] * I4v
    + rewrite_groups["THREE"] * I3v
    + rewrite_groups["TWO"] * I2v
)
if sp.expand(reconstruction - rho_integral) != 0:
    print("REWRITE_RECONSTRUCTION_FAILED; falling back to residual grouping only")
    use_rewrite = False
else:
    print("REWRITE_RECONSTRUCTION_OK=1")
    use_rewrite = True

emit_groups = rewrite_groups if use_rewrite else groups
print("GROUPING=" + ("REWRITE_I4_I3_I2" if use_rewrite else "RESIDUAL_ONLY"))

if os.environ.get("EMIT_GROUPS", "1") == "1":
    for name, coefficient in emit_groups.items():
        gens = (L, *dynamic)
        terms = 0 if coefficient == 0 else len(sp.Poly(coefficient, *gens).terms())
        free = ",".join(sorted(str(symbol) for symbol in coefficient.free_symbols)) or "-"
        wts = sorted(weighted_degree(coefficient, gens)) if coefficient != 0 else [0]
        print(f"DEGREE_ZERO_GROUP_{name} TERMS={terms} WEIGHTS={wts} FREE={free}")
        print("DEGREE_ZERO_GROUP_BEGIN_" + name)
        print(sp.factor(coefficient))
        print("DEGREE_ZERO_GROUP_END_" + name)

# I2 as a polynomial in residual constants, for the Lean definition.
print(f"I2_TERMS={len(sp.Poly(I2v, *generators).terms())}")
print("FIRST_INTEGRAL_TWO_BEGIN")
print(sp.factor(I2v))
print("FIRST_INTEGRAL_TWO_END")

# Grouped integer scale of the native (P,...,V) primitive.
native_alpha = P - sp.Rational(4, 3) * A
native_beta = Q - sp.Rational(4, 3) * B - sp.Rational(7, 6) * L * A
native_gamma = R - (
    sp.Rational(4, 3) * C0
    + sp.Rational(2, 9) * A ** 2
    + sp.Rational(7, 6) * L * B
    + native_alpha * A
)
native_delta = S - (
    sp.Rational(4, 3) * D
    + sp.Rational(4, 9) * A * B
    + L * (sp.Rational(7, 6) * C0 + sp.Rational(7, 72) * A ** 2)
    + native_alpha * B
    + sp.Rational(5, 6) * native_beta * A
)
native_epsilon = T - (
    sp.Rational(4, 3) * E
    + sp.Rational(2, 9) * B ** 2
    + sp.Rational(4, 9) * A * C0
    - sp.Rational(4, 81) * A ** 3
    + L * (sp.Rational(7, 6) * D + sp.Rational(7, 36) * A * B)
    + native_alpha * C0
    + sp.Rational(5, 6) * native_beta * B
    + sp.Rational(2, 3) * native_gamma * A
)
native_zeta = U - (
    sp.Rational(4, 9) * B * C0
    + sp.Rational(4, 9) * A * D
    - sp.Rational(4, 27) * A ** 2 * B
    + L
    * (
        sp.Rational(7, 6) * E
        + sp.Rational(7, 72) * B ** 2
        + sp.Rational(7, 36) * A * C0
        - sp.Rational(35, 1296) * A ** 3
    )
    + native_alpha * D
    + native_beta * (sp.Rational(5, 6) * C0 - sp.Rational(5, 72) * A ** 2)
    + sp.Rational(2, 3) * native_gamma * B
    + sp.Rational(1, 2) * native_delta * A
)
native_eta = V - (
    sp.Rational(2, 9) * C0 ** 2
    + sp.Rational(4, 9) * B * D
    + sp.Rational(4, 9) * A * E
    - sp.Rational(4, 27) * A * B ** 2
    - sp.Rational(4, 27) * A ** 2 * C0
    + sp.Rational(5, 243) * A ** 4
    + L
    * (
        sp.Rational(7, 36) * B * C0
        + sp.Rational(7, 36) * A * D
        - sp.Rational(35, 432) * A ** 2 * B
    )
    + native_alpha * E
    + native_beta * (sp.Rational(5, 6) * D - sp.Rational(5, 36) * A * B)
    + native_gamma * (sp.Rational(2, 3) * C0 - sp.Rational(1, 9) * A ** 2)
    + sp.Rational(1, 2) * native_delta * B
    + sp.Rational(1, 3) * native_epsilon * A
)
native_rho = sp.expand(
    rho_integral.subs(
        {
            ca: native_alpha,
            cb: native_beta,
            cg: native_gamma,
            cd: native_delta,
            ce: native_epsilon,
            cz: native_zeta,
            cet: native_eta,
        }
    )
)
print(f"NATIVE_RHO_WEIGHTS={sorted(weighted_degree(native_rho, base_symbols))}")
print(f"NATIVE_RHO_TERMS={len(sp.Poly(native_rho, *base_symbols).terms())}")
_, grouped_scale, grouped_content = content_and_scale(native_rho, base_symbols)
print(f"GROUPED_INTEGER_SCALE={grouped_scale}")
print(f"GROUPED_CONTENT={grouped_content}")

# Weighted homogeneity on native coordinates: t-scaling of weights.
ss = sp.symbols("s")
scaled = native_rho.subs(
    {
        L: ss * L,
        A: ss ** 2 * A,
        B: ss ** 3 * B,
        C0: ss ** 4 * C0,
        D: ss ** 5 * D,
        E: ss ** 6 * E,
        P: ss ** 2 * P,
        Q: ss ** 3 * Q,
        R: ss ** 4 * R,
        S: ss ** 5 * S,
        T: ss ** 6 * T,
        U: ss ** 7 * U,
        V: ss ** 8 * V,
    }
)
if sp.expand(scaled - ss ** 13 * native_rho) != 0:
    raise RuntimeError("native primitive is not weighted-homogeneous of weight 13")
print("NATIVE_WEIGHTED_HOMOGENEOUS_13=1")

# I2 native form, for the Lean definition in residual arguments.
native_I2 = sp.expand(
    I2v.subs(
        {
            ca: native_alpha,
            cb: native_beta,
            cg: native_gamma,
            cd: native_delta,
            ce: native_epsilon,
            cz: native_zeta,
            cet: native_eta,
        }
    )
)
# Keep I2 in residual coordinates (ca,...,cet) for the Lean def matching I4/I3.
print(f"I2_RESIDUAL_WEIGHTS={sorted(weighted_degree(I2v))}")

if os.environ.get("EMIT_LEAN", "1") == "1":
    print("LEAN_FIRST_INTEGRAL_TWO_BEGIN")
    print(lean_fraction(I2v, (L, *dynamic, *constant_residuals)))
    print("LEAN_FIRST_INTEGRAL_TWO_END")
    for name, coefficient in emit_groups.items():
        print(f"LEAN_GROUP_{name}_BEGIN")
        print(lean_fraction(coefficient, (L, *dynamic)))
        print(f"LEAN_GROUP_{name}_END")

# Certificate: d(rho) - (U dE - D dV) is in the span of d(residuals), d(I4),
# d(I3), d(I2), and dL  (i.e. modulo rows h11..h2, since those rows are the
# derivatives of the residuals and of I4, I3, I2).
if os.environ.get("EMIT_CERTIFICATES", "1") == "1":
    dL, dA, dB, dC0, dD, dE, dP, dQ, dR, dS, dT, dU, dV = sp.symbols(
        "dL dA dB dC0 dD dE dP dQ dR dS dT dU dV"
    )
    derivative_symbols = (dL, dA, dB, dC0, dD, dE, dP, dQ, dR, dS, dT, dU, dV)

    def total_derivative(expression: sp.Expr) -> sp.Expr:
        return sp.expand(
            sum(
                sp.diff(expression, variable) * derivative
                for variable, derivative in zip(base_symbols, derivative_symbols)
            )
        )

    native_I4 = sp.expand(
        I4v.subs(
            {
                ca: native_alpha,
                cb: native_beta,
                cg: native_gamma,
                cd: native_delta,
                ce: native_epsilon,
                cz: native_zeta,
                cet: native_eta,
            }
        )
    )
    native_I3 = sp.expand(
        I3v.subs(
            {
                ca: native_alpha,
                cb: native_beta,
                cg: native_gamma,
                cd: native_delta,
                ce: native_epsilon,
                cz: native_zeta,
                cet: native_eta,
            }
        )
    )
    row_zero_native = U * dE - D * dV
    d_rho = total_derivative(native_rho)
    # Subtract the last row and the I4/I3/I2 corrections with the residual-free
    # (or residual-dependent) multipliers pulled back to native coordinates.
    m4_native = sp.expand(
        candidate_four.subs(
            {
                ca: native_alpha,
                cb: native_beta,
                cg: native_gamma,
                cd: native_delta,
                ce: native_epsilon,
                cz: native_zeta,
                cet: native_eta,
            }
        )
    )
    m3_native = sp.expand(
        candidate_three.subs(
            {
                ca: native_alpha,
                cb: native_beta,
                cg: native_gamma,
                cd: native_delta,
                ce: native_epsilon,
                cz: native_zeta,
                cet: native_eta,
            }
        )
    )
    m2_native = sp.expand(
        candidate_two.subs(
            {
                ca: native_alpha,
                cb: native_beta,
                cg: native_gamma,
                cd: native_delta,
                ce: native_epsilon,
                cz: native_zeta,
                cet: native_eta,
            }
        )
    )
    target = sp.expand(
        d_rho
        - row_zero_native
        - m4_native * total_derivative(native_I4)
        - m3_native * total_derivative(native_I3)
        - m2_native * total_derivative(native_I2)
    )
    residual_forms = (
        total_derivative(native_alpha),
        total_derivative(native_beta),
        total_derivative(native_gamma),
        total_derivative(native_delta),
        total_derivative(native_epsilon),
        total_derivative(native_zeta),
        total_derivative(native_eta),
        dL,
    )
    cert_unknowns = sp.symbols(
        "cert_alpha cert_beta cert_gamma cert_delta cert_epsilon cert_zeta cert_eta cert_L"
    )
    cert_equations = [
        sp.expand(
            target.coeff(derivative)
            - sum(
                unknown * form.coeff(derivative)
                for unknown, form in zip(cert_unknowns, residual_forms)
            )
        )
        for derivative in derivative_symbols
    ]
    cert_solutions = list(sp.linsolve(cert_equations, cert_unknowns))
    if len(cert_solutions) != 1:
        raise RuntimeError(
            f"certificate transport did not have a unique solution ({len(cert_solutions)})"
        )
    cert_solution = cert_solutions[0]
    leftover = sp.expand(
        target
        - sum(value * form for value, form in zip(cert_solution, residual_forms))
    )
    if leftover != 0:
        raise RuntimeError("certificate transport reconstruction is nonzero")
    print("CERTIFICATE_D_RHO_EQ_ROW0_MODULO_H11_H2=1")
    for label, value in zip(
        ("ALPHA", "BETA", "GAMMA", "DELTA", "EPSILON", "ZETA", "ETA", "L"),
        cert_solution,
    ):
        print(f"DEGREE_ZERO_CERTIFICATE_{label}={sp.factor(value)}")

print(f"SCRIPT_SHA256={sha256(Path(__file__).read_bytes()).hexdigest()}")
print("STEP=5")
print("PRIMITIVE_WEIGHT=13")
print("CLEARING=65")
print("NEXT_UNUSED_ROW=h1")
print("RESIDUAL=degreeZeroPrimitive68")
checkpoint("DONE")
