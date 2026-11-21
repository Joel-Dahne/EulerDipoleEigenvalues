#!/usr/bin/env python3
"""Reproduce the odd-in-b power tables and search for dyadic strip certificates.

This standalone exact-arithmetic check does not supply proof evidence to Lean.
"""
import argparse
from fractions import Fraction
from functools import lru_cache
from math import factorial, lcm

import sympy as sp

from verify_mixed_odd_a import bernstein_1d, lean_table

H, K, LOG = sp.symbols('h k L')


def power_polynomials():
    h, k = H, K
    s, r = h + k, 2 - h**2 - k**2
    u, v = 1 - h**2, 1 - k**2
    f = (10000 + 4132*k**2 + 2167*k**3 - 2011*h*k - 7640*h*k**2
         - 226*h**2 + 3795*h**2*k - 834*h**3 + h*(808*k + 2505*k**2)*LOG)
    d, c = h**2*s + 2*h*u, 2*h**2

    def dx(p):
        return sp.diff(p, h) + sp.diff(p, LOG)/h

    g = k*f - v*sp.diff(f, k)
    ax = sp.expand(-d*s*dx(f) + c*g)
    by = sp.expand(-c*u*v*dx(f) + d*s*g)
    # Multiplication by 10^6 * S^3 * R clears all denominators.
    flux = -h*s*ax + u*(s*dx(ax) - 2*ax) + s*sp.diff(by, k) - 2*by
    potential = -h**2*r**2 + 2*h*u*s*r - 2*u**2*s**2
    pol = sp.Poly(sp.expand(100*(r*flux + s*potential*f) - h**2*s**3*r*f), LOG)
    assert pol.degree() == 1
    a, b = (sp.Poly(pol.nth(i), h, k) for i in range(2))
    assert a.degree_list() == (10, 8) and b.degree_list() == (8, 7)
    return a, b


def rows(p):
    n, m = p.degree_list()
    return [[Fraction(p.nth(i, j)) for j in range(m+1)] for i in range(n+1)]


def integer_bernstein(p):
    table = rows(p)
    cols = [bernstein_1d(col, 0, 1) for col in zip(*table)]
    coeffs = [bernstein_1d(row, 0, 1) for row in zip(*cols)]
    scale = lcm(*(v.denominator for row in coeffs for v in row))
    return tuple(tuple(int(scale*v) for v in row) for row in coeffs)


def midpoint(row):
    """Return the two midpoint restrictions, each scaled by 2^degree."""
    d = len(row)-1
    left, right = [row[0] << d], [row[-1] << d]
    while d:
        d -= 1
        row = tuple(a+b for a, b in zip(row, row[1:]))
        left.append(row[0] << d)
        right.append(row[-1] << d)
    return tuple(left), tuple(reversed(right))


def split(table, axis):
    if axis == 1:
        return tuple(zip(*(midpoint(row) for row in table)))
    return tuple(tuple(zip(*t)) for t in zip(*(midpoint(col) for col in zip(*table))))


def nonnegative(t):
    return all(x >= 0 for row in t for x in row)


def strip_polynomials(a, b, j):
    z = sp.Symbol('z')
    s = sp.Rational(1, 2)**j
    h = s*(1-z/2)
    a, b = (p.as_expr().subs(H, h) for p in (a, b))
    taylor = -sum((z/2)**m/sp.Integer(m) for m in range(1, 15))
    lo2 = sum(2*sp.Rational(1, 3)**(2*m+1)/(2*m+1) for m in range(20))
    hi2 = lo2 + 2*sp.Rational(1, 3)**41/(41*(1-sp.Rational(1, 9)))
    lower = h*(a+b*(-j*hi2+taylor)) - s*b*(z/2)**15/15
    upper = a+b*(-j*lo2+taylor)
    return tuple(sp.Poly(p, z, K) for p in (lower, upper))


def lean_strip(j, polynomials, tree, replay=False):
    def lean_tree(t):
        if t is None:
            return '.leaf'
        axis, l, r = t
        return f'(.split {str(bool(axis)).lower()} {lean_tree(l)} {lean_tree(r)})'

    def print_row(row, last):
        entries = list(map(str, row))
        # Wrap before large integer literals to keep the generated file readable.
        chunks = [[entries[0]]]
        for e in entries[1:]:
            if sum(map(len, chunks[-1]))+len(e)+2*len(chunks[-1]) > 90:
                chunks.append([e])
            else:
                chunks[-1].append(e)
        print('  #v[' + ',\n    '.join(', '.join(line) for line in chunks) + (']]' if last else '],'))

    if not replay:
        print(f'/-- Common midpoint schedule for strip {j}. -/')
        print(f'def oddBTree{j} : BernsteinMidTree :=\n  {lean_tree(tree)}\n')
    for p, label in zip(polynomials, ('Lower', 'Upper')):
        coeffs = rows(p)
        scale = lcm(*(v.denominator for row in coeffs for v in row))
        n, m = p.degree_list()
        name = f'oddB{label}{j}'
        def table(term, data):
            print(f'{term} : BernsteinIntTable {n} {m} := #v[')
            for i, row in enumerate(data):
                print_row(row, i == n)
            print()

        ints = [[int(scale*v) for v in row] for row in coeffs]
        if not replay:
            print(f'/-- Common power denominator of the {label.lower()} endpoint on strip {j}. -/')
            print(f'def {name}Scale : ℕ := {scale}\n')
            print(f'/-- Integer power coefficients of the {label.lower()} endpoint on strip {j}. -/')
            table(f'def {name}Power', ints)
            continue

        def axis(row):
            degree = len(row)-1
            return [int(factorial(degree)*v) for v in bernstein_1d(row, 0, 1)]

        middle = [axis(row) for row in ints]
        root = tuple(zip(*map(axis, zip(*middle))))
        table(f'private def {name}Middle', middle)
        table(f'private def {name}Root', root)
        print(f'private theorem {name}Root_eq : bernsteinIntFromPower {name}Power = {name}Root :=')
        print(f'  bernsteinIntFromPower_eq (middle := {name}Middle) (by decide +kernel)')
        print('    (by decide +kernel)\n')

        def replay_node(node, data, parent):
            if node is None:
                print(f'private theorem {parent}_check : BernsteinMidTree.leaf.check {parent} = true := by')
                print('  decide +kernel\n')
                return
            direction, l, r = node
            left, right = split(data, direction)
            table(f'private def {parent}L', left)
            replay_node(l, left, parent+'L')
            table(f'private def {parent}R', right)
            replay_node(r, right, parent+'R')
            print(f'private theorem {parent}_check :')
            print(f'    ({lean_tree(node)} : BernsteinMidTree).check {parent} = true :=')
            print('  BernsteinMidTree.check_split (by decide +kernel) (by decide +kernel)')
            print(f'    {parent}L_check {parent}R_check\n')

        replay_node(tree, root, name+'Root')
        print(f'/-- Kernel-checked integer subdivision signs for the {label.lower()} endpoint. -/')
        print(f'theorem {name}_check : oddBTree{j}.check (bernsteinIntFromPower {name}Power) = true := by')
        print(f'  rw [{name}Root_eq]')
        print(f'  exact {name}Root_check\n')


def optimal_tree(roots, max_x=5, max_y=6):
    """Find a minimum-node common tree within the two axis depth bounds."""
    @lru_cache(None)
    def table(root, x, nx, y, ny):
        if ny:
            return split(table(root, x, nx, y//2, ny-1), 1)[y % 2]
        if nx:
            return split(table(root, x//2, nx-1, 0, 0), 0)[x % 2]
        return roots[root]

    @lru_cache(None)
    def solve(x, nx, y, ny):
        if all(nonnegative(table(r, x, nx, y, ny)) for r in range(len(roots))):
            return 1, 0, None
        candidates = []
        if nx < max_x:
            candidates.append((0, solve(x*2, nx+1, y, ny), solve(x*2+1, nx+1, y, ny)))
        if ny < max_y:
            candidates.append((1, solve(x, nx, y*2, ny+1), solve(x, nx, y*2+1, ny+1)))
        return min(((1+l[0]+r[0], 1+max(l[1], r[1]), (axis, l[2], r[2]))
                    for axis, l, r in candidates), default=(float('inf'), 0, None),
                   key=lambda t: t[:2])

    n, depth, tree = solve(0, 0, 0, 0)
    assert n != float('inf')

    def replay(tables, node):
        if node is None:
            assert all(map(nonnegative, tables))
        else:
            axis, left, right = node
            l, r = zip(*(split(t, axis) for t in tables))
            replay(l, left)
            replay(r, right)

    replay(roots, tree)
    return n, depth, tree


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--lean-power', action='store_true', help='emit the two integer power tables')
    group.add_argument('--trees', action='store_true', help='print the common strip trees')
    group.add_argument('--lean-strips', action='store_true', help='emit power tables and trees')
    group.add_argument('--lean-replay', type=int, choices=range(10),
                       help='emit checked intermediate tables and proofs for one strip')
    args = parser.parse_args()
    a, b = power_polynomials()
    if args.lean_power:
        for name, p in [('A', a), ('B', b)]:
            lean_table('mixedOddB'+name+'Int',
                       'Integer power coefficients of the odd-in-b polynomial '+name+'.', rows(p))
        return
    if args.lean_replay is not None:
        j = args.lean_replay
        polys = strip_polynomials(a, b, j)
        tree = optimal_tree(tuple(map(integer_bernstein, polys)))[2]
        lean_strip(j, polys, tree, replay=True)
        return
    for p in (-b, a-6*b):
        assert nonnegative(integer_bernstein(sp.Poly(p.as_expr().subs(H, H/1024), H, K)))
    total_nodes, total_leaves = 2, 2
    for j in range(10):
        polys = strip_polynomials(a, b, j)
        n, depth, tree = optimal_tree(tuple(map(integer_bernstein, polys)))
        if args.lean_strips:
            lean_strip(j, polys, tree)
            continue
        print(f'Strip {j}: {n} nodes per endpoint, depth {depth}')
        if args.trees:
            print(tree)
        total_nodes += 2*n
        total_leaves += n+1
    if not args.lean_strips:
        print(f'{total_nodes} nodes, {total_leaves} leaves including the two small-strip checks')


if __name__ == '__main__':
    main()
