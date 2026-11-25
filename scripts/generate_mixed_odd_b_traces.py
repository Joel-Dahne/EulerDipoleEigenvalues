#!/usr/bin/env python3
"""Regenerate or check the Lean Horner traces for cert:odd-b-strips (strips 1–9)."""

import argparse
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import sys
from textwrap import wrap

from mixed_odd_b_trace_boxes import (
    AC, BC, AHC, BHC, G, ROOT, S, add, leaves, log_two_bounds, search, windows,
)

CAP = 8_000
STYLE_LINE_LENGTH = 100
BASE = 'EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBTrace'
OUT = ROOT / BASE.replace('.', '/')


def q(scaled):
    f = Q(scaled, S)
    return str(f.numerator) if f.denominator == 1 else f"({f.numerator} / {f.denominator})"


def horner_term(coeffs, x):
    acc = '0'
    for c in reversed(coeffs):
        if acc == '0':
            acc = c
        elif c == '0':
            acc = f'({acc} * {x})'
        else:
            acc = f'({c} + {acc} * {x})'
    return acc


def column_defs(form, count):
    fields = {
        'A': 'horner 11 (fun i => (mixedOddBAInt i {j} : ℝ)) h',
        'B': 'horner 9 (fun i => (bPadded i {j} : ℝ)) h',
        'DH_A': 'horner 10 (fun i => (i.val + 1 : ℝ) * (mixedOddBAInt i.succ {j} : ℝ)) h',
        'DH_B': 'horner 8 (fun i => (i.val + 1 : ℝ) * (bPadded i.succ {j} : ℝ)) h',
    }
    args = '(h : ℝ)' if form == 'B' else '(h l : ℝ)'
    for j in range(count):
        jfin = f'({j} : Fin 9)'
        u = fields['DH_A' if form == 'DH' else 'A'].format(j=jfin)
        v = fields['DH_B' if form == 'DH' else 'B'].format(j=jfin)
        binders = '(h _l : ℝ)' if j == 8 else args
        yield f'noncomputable def {form}{j} {binders} : ℝ :='
        if form == 'B':
            yield f'  {v}'
        elif j == 8:
            yield f'  {u}'
        else:
            yield f'  {u} +'
            yield f'    {v} * l'
        yield ''


def expr_identity(fn, form, name, k_derivative=False):
    args = 'h k' if form == 'B' else 'h k l'
    cols = [f'({form}{j} h' + (')' if form == 'B' else ' l)') for j in range(8 if form == 'B' else 9)]
    if k_derivative:
        cols = [cols[1], *(f'({cols[j]} * {j})' for j in range(2,len(cols)))]
    rhs = horner_term(cols,'k')
    yield f'theorem {name} ({args} : ℝ) : {fn} {args} ='
    yield from wrap(rhs, 98, initial_indent='    ', subsequent_indent='    ', break_long_words=False)
    yield '    := by'
    if k_derivative:
        yield '  rw [groupedDK_eq]'
    else:
        yield f'  unfold {fn}'
    defs = ', '.join(f'{form}{j}' for j in range(8 if form == 'B' else 9))
    yield from wrap(f'  norm_num [horner, {defs}, bPadded, mixedOddBAInt, mixedOddBBInt,',
                    STYLE_LINE_LENGTH, subsequent_indent='    ', break_long_words=False)
    yield "    Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_zero',"
    if k_derivative:
        yield "    Matrix.cons_val_succ, Matrix.cons_val_succ', mul_comm (2 : ℝ), mul_comm (3 : ℝ),"
        yield '    mul_comm (4 : ℝ), mul_comm (5 : ℝ), mul_comm (6 : ℝ), mul_comm (7 : ℝ), mul_comm (8 : ℝ)]'
    else:
        yield "    Matrix.cons_val_succ, Matrix.cons_val_succ']"
    yield ''


def normalize_columns(form, ac, bc):
    def term(c):
        return horner_term(list(map(str, c)), 'h')
    for j in range(len(ac) if ac else len(bc)):
        nm = f'{form}{j}'
        args = 'h' if not ac else 'h l'
        rhs = term(ac[j]) if ac else term(bc[j])
        if ac and j < len(bc):
            rhs += f' + {term(bc[j])} * l'
        yield f'theorem {nm}_eq ({args} : ℝ) : {nm} {args} ='
        yield from wrap(rhs, 98, initial_indent='    ', subsequent_indent='    ', break_long_words=False)
        yield '    := by'
        yield f'  norm_num [{nm}, horner, bPadded, mixedOddBAInt, mixedOddBBInt,'
        yield "    Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_zero',"
        yield "    Matrix.cons_val_succ, Matrix.cons_val_succ']"
        yield ''


class Trace:
    def __init__(self, lines, rat):
        self.lines = lines
        self.rat = rat

    def line(self, text):
        self.lines.append('  '+text)

    def point(self, val):
        return f'(realPoint ({self.rat(val)} : ℝ))', (Q(val), Q(val))

    def step(self, name, coeff, acc, var, interval):
        s, t = G.mul(tuple(int(x*S) for x in acc[1]), interval)
        low, high = coeff[1][0]+Q(s,S), coeff[1][1]+Q(t,S)
        self.line(f'have {name} := realHornerStep (lo := ({self.rat(low)} : ℝ))')
        self.line(f'  (hi := ({self.rat(high)} : ℝ))')
        self.line(f'  {coeff[0]} {acc[0]} h{var} h{var}₀ (by norm_num) (by norm_num)')
        return name,(low,high)

    def horner(self, name, coeffs, v, V):
        acc = coeffs[-1]
        for i in range(len(coeffs)-2,-1,-1):
            acc = self.step(f'{name}{i}',coeffs[i],acc,v,V)
        return acc

    def column(self, name, coeffs, h):
        c = list(coeffs)
        while len(c)>1 and c[-1]==0:
            c.pop()
        return self.horner(name,[self.point(t) for t in c],'H',h)


class StripTrace:
    """Render a dyadic coverage tree, sharing horizontal bounds across leaves."""

    def __init__(self, strip):
        self.strip = strip
        self.sub = Path(f'Strip{strip}')
        self.namespace = f'EulerDipoleEigenvalues.MixedOddBTrace.Strip{strip}'
        # Retain the original strip-4 proof and use its polynomial formulae
        # from the other strips. The scaled support takes one strip hypothesis
        # in place of strip 4's two bounds.
        self.scaled = strip != 4
        self.strip_arg = f'{strip} ' if self.scaled else ''
        self.strip_proof = ('(by constructor <;> norm_num)' if self.scaled else
                            '(by norm_num) (by norm_num)')
        self.formula_namespace = 'Strip4.' if self.scaled else ''
        self.files = {}

    def header(self, imports):
        # Preserve these historical source comments for byte-for-byte replay.
        original = 'generate_remaining_mixed_odd_b.py' if self.scaled else 'generate_strip_four.py'
        opened = 'open Set Scaled' if self.scaled else 'open Set'
        return ['module', '', *(f'public import {BASE}.{i}' for i in imports), '',
                f'/-! Generated by `scratch/{original}`. -/', '',
                '@[expose] public section', '', f'namespace {self.namespace}', '', opened, '']

    def emit(self, path, lines):
        self.files[Path(path)] = '\n'.join([*lines, f'end {self.namespace}', ''])

    def q(self, x):
        literal = q(x)
        return f'({literal})' if self.scaled and literal.startswith('-') else literal

    def rat(self, x):
        x = Q(x)
        if x.denominator == 1:
            return f'({x.numerator})' if self.scaled and x < 0 else str(x.numerator)
        return f'({x.numerator} / {x.denominator})'

    def interval(self, t):
        return f'Icc {self.q(t[0])} {self.q(t[1])}'

    def box_type(self, box):
        return f'Box {self.strip_arg}' + ' '.join(self.q(t) for pair in box for t in pair)

    def formulae(self):
        self.emit('Strip4Formulae.lean', [*self.header(['Strip4Support']),
             *column_defs('C', 9), *column_defs('DH', 9), *column_defs('B', 8),
             *expr_identity('grouped', 'C', 'formula'),
             *expr_identity('groupedDK', 'C', 'formulaK', True),
             *expr_identity('groupedDH', 'DH', 'formulaH'),
             *expr_identity('groupedB', 'B', 'formulaB'),
             *normalize_columns('C', AC, BC), *normalize_columns('DH', AHC, BHC),
             *normalize_columns('B', [], BC)])

    def column_line(self, tag, name, j, h, l):
        qualified = f'{name}{j}'
        lines = []
        tr = Trace(lines, self.rat)
        tr.line(f'have hH₀ : (0 : ℝ) ≤ {self.q(h[0])} := by norm_num')
        if name=='B':
            r=tr.column('hB',BC[j],h)
        else:
            ac,bc=(AC,BC) if name=='C' else (AHC,BHC)
            r=tr.column('hA',ac[j],h)
            if j<len(bc):
                tr.line('have hL := realNegBounds hLog')
                tr.line(f'have hL₀ : (0 : ℝ) ≤ -({self.q(l[1])}) := by norm_num')
                bb=tr.column('hB',bc[j],h)
                neg=(f'(realNegBounds {bb[0]})', (-bb[1][1], -bb[1][0]))
                r=tr.step('hc',r,neg,'L',(-l[1],-l[0]))
        hlog = name!='B' and j<8
        form=f'{self.formula_namespace}{qualified} h'+(' l' if name!='B' else '')
        intro=[f'theorem {tag}{qualified} {{h'+(' l' if name!='B' else '')+' : ℝ}',
               f'    (hH : h ∈ {self.interval(h)})']
        if hlog:
            intro.append(f'    (hLog : l ∈ {self.interval(l)})')
        intro.append(f'    : {form} ∈ Icc {self.rat(r[1][0])} {self.rat(r[1][1])} := by')
        end=[f'  rw [{self.formula_namespace}{qualified}_eq]',
             f'  simpa only [neg_mul_neg, zero_mul, zero_add, add_zero] using {r[0]}', '']
        return [*intro,*lines,*end],r[1]


    def proof_window(self, name, h, l):
        head = f'theorem {name} : Window {self.strip_arg}{self.q(h[0])} {self.q(h[1])}'
        tail = f'{self.q(l[0])} {self.q(l[1])} :='
        declaration = ([f'{head} {tail}'] if len(head) + 1 + len(tail) <= STYLE_LINE_LENGTH
                       else [head, f'    {tail}'])
        return [*declaration, f'  window {self.strip_proof}',
                '    (by norm_num [X, certificateLogTaylor, Finset.sum_range_succ])',
                '    (by norm_num [X, certificateLogTaylor, Finset.sum_range_succ])', '']


    def slab(self, i, h, proofs):
        """Share column bounds and log windows among leaves with the same h range."""
        tag=f'h{i:02}'
        a,b=h;m=(a+b)//2
        e,l,le,lm=windows(self.strip,h)
        lines=self.header(['Strip4Formulae', 'Scaled'] if self.scaled else ['Strip4Formulae'])
        cols={}
        for group,form,region,log in [('C','C',h,l), ('W','C',h,le),('M','C',(m,m),lm),
                                      ('H','DH',h,le),('B','B',h,le)]:
            if group=='C' and 'plain' not in proofs or group!='C' and 'centered' not in proofs:
                continue
            cols[group]=[]
            for j in range(8 if form=='B' else 9):
                code, data=self.column_line(tag+group,form,j,region,log)
                lines+=code
                args=('(l := l) ' if form!='B' and j==8 else '') + 'hH' + (' hLog' if form!='B' and j<8 else '')
                cols[group].append((f'({tag+group+form}{j} {args})',data))
        lines+=self.proof_window(tag+'Window',h,l)
        if 'centered' in proofs:
            ml=(lm[0]+e,lm[1]-e)
            lines+=self.proof_window(tag+'MidWindow',(m,m),ml)
            lines += [
                f'theorem {tag}Gap : Gap {self.strip_arg}{self.q(a)} {self.q(b)} {self.q(e)} :=',
                f'  gap {self.strip_proof} (by norm_num [X])', '',
                f'theorem {tag}Wide {{h off : ℝ}} (hh : h ∈ {self.interval(h)}) (he : |off| ≤ {self.q(e)}) :',
                f'    Real.log h + off ∈ {self.interval(le)} :=',
                f'  window_wide {self.strip_proof} {tag}Window (by norm_num) (by norm_num) hh he', '',
                f'theorem {tag}Mid {{off : ℝ}} (he : |off| ≤ {self.q(e)}) :',
                f'    Real.log ({self.q(m)} : ℝ) + off ∈ {self.interval(lm)} :=',
                f'  window_wide {self.strip_proof} {tag}MidWindow (by norm_num) (by norm_num)',
                '    (realPoint _) he', '',
            ]
        self.emit(self.sub/f'H{i:02}.lean',lines)
        return tag,cols


    def bounded(self, name, fn, cols, h, k, l, kd=False):
        lines = []
        tr = Trace(lines, self.rat)
        tr.line(f'have hK₀ : (0 : ℝ) ≤ {self.q(k[0])} := by norm_num')
        if kd:
            ds=[cols[1]]
            for j in range(2,9):
                tr.line(f'have hJ{j} := realPoint ({j} : ℝ)')
                tr.line(f'have hJ{j}₀ : (0 : ℝ) ≤ {j} := by norm_num')
                ds.append(tr.step(f'hD{j}',tr.point(0),cols[j],f'J{j}',(S*j,S*j)))
            cols=ds
        acc=tr.horner('hR',cols,'K',k)
        args='h k' if l is None else 'h k l'
        intro=[f'private theorem {name} {{{args} : ℝ}}',f'    (hH : h ∈ {self.interval(h)}) (hK : k ∈ {self.interval(k)})']
        if l is not None: intro.append(f'    (hLog : l ∈ {self.interval(l)})')
        intro.append(f'    : {fn} {args} ∈ Icc {self.rat(acc[1][0])} {self.rat(acc[1][1])} := by')
        formula = {'mixedOddBCleared': 'formula', 'groupedDH': 'formulaH',
                   'groupedDK': 'formulaK', 'groupedB': 'formulaB'}[fn]
        rw = ('← grouped_eq, ' if fn == 'mixedOddBCleared' else '') + self.formula_namespace + formula
        return [*intro,*lines,f'  rw [{rw}]',f'  simpa only [zero_add] using {acc[0]}',''],acc[1]


    def leaf(self, idx, box, kind, slab_data):
        tag, cols = slab_data
        h, k = box
        a, b = h
        c, d = k
        m, n = (a + b) // 2, (c + d) // 2
        name = f'leaf{idx:03}'
        _, l, le, lm = windows(self.strip, h)
        if kind=='plain':
            code,v=self.bounded(name+'Val','mixedOddBCleared',cols['C'],h,k,l)
            assert v[0]>0
            return [*code,f'theorem {name} : {self.box_type(box)} :=',
                    f'  plain {self.strip_proof} {tag}Window (fun hH hK hLog =>',
                    f'    (by norm_num : (0 : ℝ) ≤ {self.rat(v[0])}).trans ({name}Val hH hK hLog).1)', '']
        codeV,v=self.bounded(name+'Val','mixedOddBCleared',cols['M'],(m,m),(n,n),lm)
        codeH,u=self.bounded(name+'H','groupedDH',cols['H'],h,(n,n),le)
        codeK,w=self.bounded(name+'K','groupedDK',cols['W'],h,k,le,True)
        codeB,p=self.bounded(name+'B','groupedB',cols['B'],h,(n,n),None)
        extrema=[y/Q(x,S) for x in h for y in p]
        ql=Q((min(extrema)*S).__floor__(),S); qu=Q((max(extrema)*S).__ceil__(),S)
        D=max(abs(u[0]+ql),abs(u[1]+qu)); E=max(map(abs,w))
        r,s=Q(b-a,2*S),Q(d-c,2*S)
        assert v[0]>=D*r+E*s,(box,v,D,E)
        return [*codeV,*codeH,*codeK,*codeB,
                f'theorem {name} : {self.box_type(box)} := by',
                '  refine centered (m := '+self.q(m)+') (n := '+self.q(n)+')',
                f'    (r := {self.rat(r)}) (s := {self.rat(s)}) (lb := {self.rat(v[0])})',
                f'    (D := {self.rat(D)}) (E := {self.rat(E)})',
                f'    {self.strip_proof} (by constructor <;> norm_num) (by constructor <;> norm_num)',
                f'    {tag}Gap {tag}Wide {tag}Mid (by norm_num) (by norm_num)',
                '    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_',
                f'  · exact fun hl => ({name}Val (realPoint _) (realPoint _) hl).1',
                '  · intro x l hx hl',
                f'    have hd := {name}H hx (realPoint _) hl',
                f'    have hb := {name}B hx (realPoint _)',
                f'    have hq := divide (L := {self.rat(ql)}) (U := {self.rat(qu)})',
                '      (by norm_num) hx hb (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
                '    exact abs_sum_bound hd hq (by norm_num) (by norm_num)',
                '  · intro h k l hh hk hl',
                f'    have hd := {name}K hh hk hl',
                '    exact abs_le.mpr ⟨(by norm_num : _ ≤ _).trans hd.1, hd.2.trans (by norm_num)⟩', '']


    def tree_proof(self, node, ids):
        if len(node) == 2:
            return f'leaf{ids[node[0]]:03}'
        _, axis, children = node
        midpoint = self.q(children[0][0][axis][1])
        proofs = ' '.join(self.tree_proof(child, ids) for child in children)
        return f'(split{"H" if axis == 0 else "K"} (m := {midpoint}) {proofs})'


    def generate(self):
        """Return the generated files and number of leaves, without writing files."""
        strip = self.strip
        tree = search(strip, ((S >> (strip + 1), S >> strip), (0, S)))
        data = list(leaves(tree))
        groups = defaultdict(list)
        for idx, (box, kind) in enumerate(data):
            groups[box[0]].append((idx, box, kind))
        if not self.scaled:
            self.formulae()
        modules = []
        for i, (h, group) in enumerate(groups.items()):
            slab_data = self.slab(i, h, {kind for _, _, kind in group})
            head = self.header([f'Strip{strip}.H{i:02}'])
            part = []
            part_idx = 0

            def flush():
                nonlocal part, part_idx
                if part:
                    name = f'K{i:02}Part{part_idx:02}'
                    self.emit(self.sub / f'{name}.lean', [*head, *part])
                    modules.append(f'Strip{strip}.{name}')
                    part = []
                    part_idx += 1

            for idx, box, kind in group:
                code = self.leaf(idx, box, kind, slab_data)
                if len(head) + len(part) + len(code) + 2 > CAP:
                    flush()
                part.extend(code)
            flush()
        ids = {box: i for i, (box, _) in enumerate(data)}
        expr = self.tree_proof(tree, ids)
        self.emit(f'Strip{strip}Full.lean', [*self.header(modules),
            f'theorem root : {self.box_type(tree[0])} :=',
            *wrap(expr, 96, initial_indent='  ', subsequent_indent='  ', break_long_words=False), ''])
        return self.files, len(data)


# Strip 9 uses the fixed 17-box partition checked in MixedOddBStrips.lean.
STRIP_NINE_BOXES = [
    (1024, 1152, 0, 1024), (1152, 1280, 0, 1024),
    (1280, 1408, 0, 1024), (1408, 1536, 0, 1024),
    (1024, 1536, 1024, 2048), (1024, 1536, 2048, 4096),
    (1536, 1664, 0, 4096), (1664, 1792, 0, 4096),
    (1792, 2048, 0, 4096),
    *((1024, 2048, (1 << n), (2 << n)) for n in range(12, 20)),
]


def strip_nine_log_at(a):
    x = 1 - Q(a * 512, S)
    lo, hi = log_two_bounds()
    t = -sum(x**n / n for n in range(1, 15))
    return G.rational(t - 9 * hi - x**15 / (15 * (1 - x)))[0], G.rational(t - 9 * lo)[1]


def strip_nine_identity():
    ac = [horner_term(list(map(str, c)), 'h') for c in AC]
    bc = [horner_term(list(map(str, c)), 'h') for c in BC]
    cs = [f'({a} + {b} * l)' if b != '0' else a for a, b in zip(ac, [*bc, '0'])]
    rhs = horner_term(cs, 'k')
    return '\n'.join([
        'private theorem grouped_expanded (h k l : ℝ) : grouped h k l =',
        *wrap(rhs, 96, initial_indent='    ', subsequent_indent='    ', break_long_words=False,
              break_on_hyphens=False),
        '    := by',
        '  simp only [grouped, horner, bPadded, mixedOddBAInt, mixedOddBBInt, Fin.val_zero,',
        '    Fin.val_succ, Nat.reduceAdd, Nat.reduceLT, dite_true, dite_false, Matrix.cons_val_zero,',
        "    Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ', Int.cast_ofNat,",
        '    Int.cast_neg, Int.cast_zero, zero_mul, add_zero, zero_add]',
    ])


def strip_nine_trace(index, a, b, c, d):
    h, k, l = (a, b), (c, d), (strip_nine_log_at(a)[0], strip_nine_log_at(b)[1])
    assert k[0] >= 0 and h[0] > 0 and l[1] < 0
    lines = [
        f'theorem leaf{index:02d} {{h k l : ℝ}}',
        f'    (hH : h ∈ Icc {q(a)} {q(b)}) (hK : k ∈ Icc {q(c)} {q(d)})',
        f'    (hLog : l ∈ Icc {q(l[0])} {q(l[1])}) : 0 ≤ mixedOddBCleared h k l := by',
        '  have hL := realNegBounds hLog',
        f'  have hH₀ : (0 : ℝ) ≤ {q(a)} := by norm_num',
        f'  have hK₀ : (0 : ℝ) ≤ {q(c)} := by norm_num',
        f'  have hL₀ : (0 : ℝ) ≤ -({q(l[1])}) := by norm_num',
    ]

    def step(name, coeff, acc, var, interval):
        lb, ub = add(coeff[1], G.mul(acc[1], interval))
        lines.extend([
            f'  have {name} := realHornerStep (lo := ({q(lb)} : ℝ))',
            f'    (hi := ({q(ub)} : ℝ))',
            f'    {coeff[0]} {acc[0]} h{var} h{var}₀ (by norm_num) (by norm_num)',
        ])
        return name, (lb, ub)

    def column(name, coefficients):
        acc = None
        for i, coeff in reversed(list(enumerate(coefficients))):
            point = f'(realPoint ({coeff} : ℝ))', (S * coeff, S * coeff)
            if acc is not None:
                acc = step(f'h{name}_{i}', point, acc, 'H', h)
            elif coeff != 0:
                acc = point
        assert acc is not None
        return acc

    coeff = []
    for j, ac in enumerate(AC):
        aa = column(f'A{j}', ac)
        if j < len(BC):
            bb = column(f'B{j}', BC[j])
            negbb = f'(realNegBounds {bb[0]})', (-bb[1][1], -bb[1][0])
            coeff.append(step(f'hC{j}', aa, negbb, 'L', (-l[1], -l[0])))
        else:
            coeff.append(aa)
    acc = coeff[-1]
    for i in range(len(coeff) - 2, -1, -1):
        acc = step(f'hR{i}', coeff[i], acc, 'K', k)
    assert acc[1][0] > 0
    lines.extend([
        f'  have hp : 0 ≤ ({q(acc[1][0])} : ℝ) := by norm_num',
        '  refine hp.trans ?_',
        '  rw [← grouped_eq, grouped_expanded]',
        f'  simpa only [neg_mul_neg, zero_mul, zero_add] using {acc[0]}.1',
    ])
    return '\n'.join(lines)


def strip_nine_source():
    head = '''module

public import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBTrace.Basic

/-!
# Explicit Horner traces for strip 9

Generated by `scratch/generate_mixed_odd_b_strip_nine.py`. Each bound is checked
in Lean. The horizontal, vertical and logarithm endpoints are in real units.
-/

public section

namespace EulerDipoleEigenvalues.MixedOddBTrace.Strip9

open Set'''
    return '\n\n'.join([
        head, strip_nine_identity(), *(strip_nine_trace(i, *box) for i, box in enumerate(STRIP_NINE_BOXES)),
        'end EulerDipoleEigenvalues.MixedOddBTrace.Strip9',
    ]) + '\n'


def generated_paths(directory, strip):
    """List existing generated Lean files for this strip (not support modules)."""
    if strip == 9:
        candidates = [directory / 'Strip9.lean']
    else:
        candidates = [*(directory / f'Strip{strip}').rglob('*.lean'),
                      directory / f'Strip{strip}Full.lean']
        if strip == 4:
            candidates.append(directory / 'Strip4Formulae.lean')
    return {p.relative_to(directory) for p in candidates if p.is_file()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true',
                        help='compare Lean sources byte for byte without rewriting them')
    parser.add_argument('--output-dir', type=Path, default=OUT,
                        help='write or check files in this directory instead of MixedOddBTrace')
    parser.add_argument('strip', type=int, nargs='*', metavar='STRIP',
                        help='strips to generate (1–9; default: all)')
    args = parser.parse_args()
    strips = sorted(set(args.strip or range(1, 10)))
    if not all(1 <= j <= 9 for j in strips):
        parser.error('strip numbers must be between 1 and 9')

    failed = False
    for j in strips:
        if j == 9:
            files = {Path('Strip9.lean'): strip_nine_source()}
            box_count = len(STRIP_NINE_BOXES)
        else:
            files, box_count = StripTrace(j).generate()

        stale = generated_paths(args.output_dir, j) - files.keys()
        for path in sorted(stale):
            print(f'unexpected generated file: {args.output_dir / path}', file=sys.stderr)
            failed = True

        line_counts = {path: len(source.splitlines()) for path, source in files.items()}
        largest = max(line_counts, key=line_counts.get)
        if line_counts[largest] > CAP:
            raise ValueError(f'{largest}: {line_counts[largest]} lines exceeds the {CAP}-line cap')
        for path, source in files.items():
            target = args.output_dir / path
            data = source.encode('utf-8')
            if target.is_file() and target.read_bytes() == data:
                continue
            if args.check:
                print(f'{"differs" if target.is_file() else "missing"}: {target}', file=sys.stderr)
                failed = True
            elif not stale:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)

        print(f'Strip {j}: {box_count} boxes, {len(files)} files, {line_counts[largest]} lines max')
    if failed:
        print('Generated sources do not match. Remove unexpected files and regenerate as needed.',
              file=sys.stderr)
    return int(failed)


if __name__ == '__main__':
    raise SystemExit(main())
