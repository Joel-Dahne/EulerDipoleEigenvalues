"""Exact dyadic box search for the mixed odd-in-b strip certificates."""

from fractions import Fraction as Q
from functools import cache
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]

TABLES = (ROOT /
          'NoEmbeddedEigenvalues/Certificates/Inequalities/MixedOddBAlgebra.lean')


def power_tables():
    source = TABLES.read_text(encoding='utf-8')
    tables = []
    for name, shape in [('A', (11, 9)), ('B', (9, 8))]:
        block = source.split(f'def mixedOddB{name}Int ', 1)[1].split('\ndef ', 1)[0]
        rows = tuple(tuple(map(int, re.findall(r'-?\d+', row)))
                     for row in re.findall(r'!\[([^\[\]]+)\]', block))
        assert len(rows) == shape[0] and all(len(row) == shape[1] for row in rows)
        tables.append(rows)
    return tables


def derivative(table, axis):
    if axis == 0:
        return tuple(tuple(i*c for c in row) for i, row in enumerate(table) if i)
    return tuple(tuple(j*c for j, c in enumerate(row) if j) for row in table)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


class DyadicGrid:
    """An interval (l,u) represents [l/scale,u/scale], scale=2**bits."""
    def __init__(self, bits):
        self.scale = 1 << bits

    def mul(self, a, b):
        products = (a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1])
        s = self.scale
        return min(products) // s, -(-max(products) // s)

    def rational(self, x):
        n, d = x.numerator*self.scale, x.denominator
        return n // d, -(-n // d)

    def horner_int(self, coefficients, x):
        t = (0, 0)
        for c in reversed(coefficients):
            c *= self.scale
            lo, hi = self.mul(t, x)
            t = lo+c, hi+c
        return t

    def affine_poly(self, a_cols, b_cols, h, k, log_h):
        """Combine A and B*log(h) by k-power before the outer Horner loop."""
        t = (0, 0)
        for i in range(len(a_cols)-1, -1, -1):
            c = self.horner_int(a_cols[i], h)
            if i < len(b_cols):
                c = add(c, self.mul(self.horner_int(b_cols[i], h), log_h))
            t = add(self.mul(t, k), c)
        return t


def log_two_bounds():
    t = Q(1, 3)
    lo = sum(2*t**(2*i+1)/(2*i+1) for i in range(20))
    return lo, lo + 2*t**41/(41*(1-t*t))


def halves(box, axis):
    lo, hi = box[axis]
    mid = (lo+hi)//2
    assert lo < mid < hi and 2*mid == lo+hi
    left, right = list(box), list(box)
    left[axis], right[axis] = (lo, mid), (mid, hi)
    return tuple(left), tuple(right)


GRID_BITS = 20
S = 1 << GRID_BITS
G = DyadicGrid(GRID_BITS)
A, B = power_tables()
AH, BH, AK, BK = derivative(A,0), derivative(B,0), derivative(A,1), derivative(B,1)
AC, BC, AHC, BHC, AKC, BKC = (list(zip(*t)) for t in (A,B,AH,BH,AK,BK))
LO2, HI2 = Q(6931471805599453,10**16), Q(6931471805599454,10**16)
assert LO2 <= log_two_bounds()[0] <= log_two_bounds()[1] <= HI2

def up(x):
    return -(-x.numerator // x.denominator)

@cache
def log_at(j,h):
    """Taylor endpoints at h/S, and the series tail before the log(2) shift."""
    x = 1 - Q((1 << j)*h,S)
    t = -sum(x**n/n for n in range(1,15))
    tail = x**15/(15*(1-x))
    return -j*HI2+t-tail, -j*LO2+t, tail

@cache
def windows(j,h):
    """Offset bound, plain window, offset-wide window, and midpoint window."""
    a,b = h
    m = (a+b)//2
    e = up((log_at(j,a)[2] + j*(HI2-LO2))*S)
    l = G.rational(log_at(j,a)[0])[0], G.rational(log_at(j,b)[1])[1]
    return e, l, (l[0]-e,l[1]+e), (G.rational(log_at(j,m)[0])[0]-e,G.rational(log_at(j,m)[1])[1]+e)

@cache
def bound(j,h,k):
    """Propose a lower bound for both Taylor endpoints on a box."""
    a,b=h; c,d=k; m,n=(a+b)//2,(c+d)//2
    e,l,le,lm = windows(j,h)
    p = G.affine_poly(AC,BC,h,k,l)[0]
    if p > 0:
        return p, 'plain'
    v = G.affine_poly(AC,BC,(m,m),(n,n),lm)[0]
    # Hold k at its midpoint on the horizontal leg; include B/h from d(log h)/dh.
    u = G.affine_poly(AHC,BHC,h,(n,n),le)
    w = G.affine_poly(BC,[],h,(n,n),le)
    # Bound the quotient by its four corners. Lean checks the bounds by
    # clearing just the positive denominator, not by evaluating reciprocals.
    corners=[Q(t*S,i) for t in w for i in h]
    ql=min(corners).__floor__(); qu=up(max(corners))
    r=max(abs(u[0]+ql),abs(u[1]+qu))
    z=max(map(abs,G.affine_poly(AKC,BKC,h,k,le)))
    val=v-up(Q(r*(b-a)+z*(d-c),2*S))
    return max(p,val), 'centered'


def search(j,box,level=0):
    """Bisect at midpoints; rank splits by number of passing children, then scores."""
    score, proof=bound(j,*box)
    if score>0:
        return box,proof
    assert level < 30, (box,score)
    def rank(children):
        a,b=sorted(bound(j,*c)[0] for c in children)
        return int(a>0)+int(b>0),a,b
    opts=[(i,halves(box,i)) for i in range(2) if box[i][1]-box[i][0]>=2]
    # Keep h before k when both splits have the same rank.
    i,children=max(opts,key=lambda p:rank(p[1]))
    return box,i,tuple(search(j,c,level+1) for c in children)


def leaves(tree):
    if len(tree)==2:
        yield tree
    else:
        for child in tree[2]:
            yield from leaves(child)
