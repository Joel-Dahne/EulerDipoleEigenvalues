#!/usr/bin/env python3
"""Reproduce the exact Odd–odd Bernstein checks in Manuscript/eigenvalues.tex.

Run with Python 3 and SymPy (`python3 scripts/verify_dd_residual.py`). This
script is an independent check, not an input to the Lean proof.
"""

from argparse import ArgumentParser
from math import comb
from time import perf_counter

from sympy import Poly, QQ, Rational, symbols

s, r, x, y = symbols("s r x y")

# Rows in the manuscript's residual table (including the zero row at k = 8).
A = sum(s**k * row for k, row in enumerate([
    452*r**4 - 832*r**3 + 1024*r**2,
    -9*r**5 + 120*r**4 + 768*r**3,
    148*r**3 + 1664*r - 4096,
    20*r**4 + 98*r**3 - 512*r**2 + 768*r,
    -32*r**2 - 384*r + 2048,
    28*r**3 + 72*r**2 - 592*r + 512,
    -8*r - 256,
    10*r**2 + 96*r - 256,
    0,
    r + 32,
]))
B = sum(s**k * row for k, row in enumerate([
    1408*r**3 - 2240*r**2,
    -87*r**4 + 96*r**3,
    528*r**2 - 512*r + 1024,
    4*r**3 - 56*r**2,
    128*r - 512,
    18*r**2 + 64*r - 128,
    64,
    -16*r + 64,
    0,
    -8,
]))


def quotients():
    """Clear the endpoint denominators and remove (1-x)^4 exactly."""
    sub = {s: 2*x, r: 2*(1 - x)*(2*x + (1 - x)*y)}
    factor = Poly((1 - x)**4, x, y, domain=QQ)
    lower = r * (A + B*(r - 2)/4)
    upper = r * (A*(r + 2)**3 + r*B*((r - 2)*(r + 2)**2/2 + (r - 2)**3/6))
    return tuple(Poly(p.subs(sub), x, y, domain=QQ).exquo(factor) for p in (lower, upper))


def bernstein_coefficients(poly, box):
    """Pull back the box, keeping degree bounds, then change basis on [0,1]^2."""
    x0, x1, y0, y1 = box
    n, m = poly.degree(x), poly.degree(y)
    a = Poly(poly.as_expr().subs({x: x0 + (x1 - x0)*x, y: y0 + (y1 - y0)*y}),
             x, y, domain=QQ).as_dict()
    return {
        (i, j): sum(c * Rational(comb(i, k), comb(n, k)) * Rational(comb(j, l), comb(m, l))
                    for (k, l), c in a.items() if k <= i and l <= j)
        for i in range(n + 1) for j in range(m + 1)
    }


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--lean-power", choices=("lower", "upper"),
                        help="print the selected quotient's power table as Lean vector literals")
    args = parser.parse_args()
    start = perf_counter()
    lower, upper = quotients()
    if args.lean_power:
        poly = lower if args.lean_power == "lower" else upper
        rows = ["![" + ", ".join(str(poly.coeff_monomial(x**k * y**l))
                                 for l in range(poly.degree(y) + 1)) + "]"
                for k in range(poly.degree(x) + 1)]
        print("![\n  " + ",\n  ".join(rows) + "]")
        return
    for name, poly in (("Q_-", lower), ("Q_+", upper)):
        print(f"{name}: bidegree {(poly.degree(x), poly.degree(y))}")
    print(f"Polynomial construction and division: {perf_counter() - start:.3f} s")
    half, quarter = Rational(1, 2), Rational(1, 4)
    corner = {(i, j) for i in range(3) for j in range(3 - i)}
    cases = [
        ("Q_-", lower, (0, half, 0, 1), Rational(1600, 21), corner),
        ("Q_-", lower, (half, 1, 0, 1), 14788, set()),
        ("Q_+", upper, (0, quarter, 0, half), Rational(9472, 4095), corner | {(3, 0)}),
        ("Q_+", upper, (quarter, half, 0, half), Rational(264237, 64), set()),
        ("Q_+", upper, (0, half, half, 1), Rational(63812, 3), set()),
        ("Q_+", upper, (half, 1, 0, 1), Rational(1181728, 3), set()),
    ]
    if (lower.degree(x), lower.degree(y), upper.degree(x), upper.degree(y)) != (9, 6, 15, 9):
        raise ValueError("Bidegrees do not match the manuscript")
    for name, poly, box, expected_min, expected_zeros in cases:
        start = perf_counter()
        b = bernstein_coefficients(poly, box)
        if min(b.values()) < 0:
            raise ValueError(f"{name} on {box}: negative Bernstein coefficient")
        positive_min = min(v for v in b.values() if v > 0)
        zeros = {ij for ij, v in b.items() if v == 0}
        if positive_min != expected_min or zeros != expected_zeros:
            raise ValueError(f"{name} on {box}: unexpected minimum or zero set: "
                             f"{positive_min}, {sorted(zeros)}")
        print(f"{name} on {box}: min positive = {positive_min}; {len(zeros)} zeros; "
              f"{perf_counter() - start:.3f} s")


if __name__ == "__main__":
    main()
