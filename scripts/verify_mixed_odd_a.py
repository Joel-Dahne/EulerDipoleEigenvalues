#!/usr/bin/env python3
"""Reproduce the mixed odd-in-a power tables; Lean checks them independently."""
import argparse
from fractions import Fraction
from math import comb, lcm

import sympy as sp


def power_tables():
    h, k, t, q = sp.symbols('h k t q')
    s, r = h + k, 2 - h**2 - k**2
    u, v = 1 - h**2, 1 - k**2
    w = 2000
    poly = (721*k**2 - 107*k**3 + 60*k**4 + 85*k**6
            + h*(-519*k - 64*k**2 - 26*k**3 - 400*k**5)
            + h**2*(-98 - 79*k**2 + 890*k**4)
            + h**3*(781 - 583*k - 842*k**3)
            + h**4*(-240 + 677*k + 124*k**2)
            + h**5*(-263 + 37*k) + 53*h**6 - h/2 - 4*k)
    m = sp.expand(2 * (poly*s**6 - 4*h**3*s**4 - 2744*h**6*s**2 + 1033*h**8
                        + 224*h**4*s**5 + 235*h**8*s))
    x, y = [sp.expand(s*m.diff(i) - 6*m) for i in (h, k)]
    xx, xy, yy = [sp.expand(s*a.diff(i) - 7*a) for a, i in ((x, h), (x, k), (y, k))]
    d, c = h**2*s + 2*h*u, 2*h**2
    dh, dk = [s*d.diff(i) - d for i in (h, k)]
    ch, ck = [s*c.diff(i) - 2*c for i in (h, k)]
    ah = 3*h*d*s**2 - u*dh*s + u*(k*c*s - v*ck)
    ak = v*(-u*ch + 3*h*c*s - dk*s) + k*d*s**2
    a0 = (d*s**2 + h*dh*s - h*k*c*s + h*v*ck)*r + s*(-h**2*r**2 + 2*h*u*s*r - 2*u**2*s**2)
    # This is 2000^2 * S^16 * R times the normalized residual.
    n = sp.Poly(w**2*a0*s**13 - (w**2//200)*h**2*r*s**16
                + (ah*x + ak*y)*w*r*s**6
                - d*r*s*(u*(w*s**6*xx + x**2) + v*(w*s**6*yy + y**2))
                - 2*c*u*v*r*(w*s**6*xy + x*y), h, k)
    assert n.degree_list() == (32, 30)
    for j, axis in enumerate((0, 1), start=1):
        terms = {}
        for (a, b), coefficient in n.terms():
            assert a+b >= 15
            terms[a+b-15, (a, b)[axis]] = int(coefficient)
        p = sp.Poly.from_dict(terms, (t, q))
        assert p.degree_list() == (17, (32, 30)[axis])
        yield j, [[int(p.nth(a, b)) for b in range(p.degree(q)+1)]
                  for a in range(p.degree(t)+1)]


def bernstein_1d(coeffs, left, right):
    """Affine power transform followed by the power-to-Bernstein transform."""
    n = len(coeffs) - 1
    powers = [(right-left)**i * sum(
        comb(k, i)*left**(k-i)*coeffs[k] for k in range(i, n+1)) for i in range(n+1)]
    return [sum(Fraction(comb(i, k), comb(n, k))*powers[k] for k in range(i+1))
            for i in range(n+1)]


def check(j, table):
    half = Fraction(1, 2)
    halves = [(0, half), (half, 1)]
    for a, b in halves:
        cols = [bernstein_1d(row, a, b) for row in zip(*table)]
        for c, d in ([(0, 1)] if j == 1 else halves):
            assert all(x >= 0 for row in zip(*cols) for x in bernstein_1d(row, c, d))


def lean_table(name, description, rows):
    print(f'/-- {description} -/')
    print(f'def {name} : Fin {len(rows)} → Fin {len(rows[0])} → ℤ := ![')
    for i, row in enumerate(rows):
        chunks = [', '.join(map(str, row[k:k+4])) for k in range(0, len(row), 4)]
        print('  ![' + ',\n    '.join(chunks) + ('],' if i+1 < len(rows) else ']]'))
    print()


def lean_first_axis(j, table):
    half = Fraction(1, 2)
    for side, a, b in [('Left', 0, half), ('Right', half, 1)]:
        rows = list(zip(*(bernstein_1d(col, a, b) for col in zip(*table))))
        scale = lcm(*(v.denominator for row in rows for v in row))
        name = f'mixedOddAAxis{j}{side}'
        lean_table(name + 'Int', f'Integer coefficients after the first-axis {side.lower()} transform.',
                   [[int(scale*v) for v in row] for row in rows])
        print(f'/-- The common denominator for `{name}Int`. -/')
        print(f'def {name}Scale : ℕ := {scale}\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-power', action='store_true', help='emit the Lean tables')
    args = parser.parse_args()
    for j, table in power_tables():
        check(j, table)
        if args.lean_power:
            lean_table(f'mixedOddAPowerInt{j}',
                       f'Power table for the scaled odd-in-a numerator in triangle {j}.', table)
            lean_first_axis(j, table)
        else:
            print(f'Triangle {j}: all Bernstein coefficients nonnegative')


if __name__ == '__main__':
    main()
