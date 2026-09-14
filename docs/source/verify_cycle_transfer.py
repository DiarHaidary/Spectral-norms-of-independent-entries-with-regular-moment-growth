"""Exact bounded tests of the same-rung Parseval/consumed cycle transfer.

Only basic rational matrix helpers are loaded from a frozen verifier; its test
suite is not run. No floating complex arithmetic or sign-law enumeration.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from hashlib import sha256
from collections import Counter
import json
import runpy

HERE = Path(__file__).resolve().parent
HELPER = HERE.parent/'mi32_profile_2026-09-13'/'verify_coherent_mark_transfer.py'
base = runpy.run_path(str(HELPER))
zero, eye, adj, scale, add, mul, gram, masks = (base[n] for n in
    ['zero', 'eye', 'adj', 'scale', 'add', 'mul', 'gram', 'masks'])
COUNT = Counter()


def eq(a, b):
    assert a == b
    COUNT['exact_equalities'] += 1


def psd(a):
    base['psd'](a)
    COUNT['exact_psd_checks'] += 1


def control(value):
    assert value
    COUNT['nonzero_or_failure_controls'] += 1


def kron(a, b):
    return [[x*y for x in ar for y in br] for ar in a for br in b]


def hstack(a, b): return [ar+br for ar, br in zip(a, b)]
def select(a, rows, cols): return [[a[i][j] for j in cols] for i in rows]


X = [[F(0), F(1)], [F(1), F(0)]]
Q = kron(eye(2), [[F(1), F(0)], [F(0), F(0)]])
DELTA = add(eye(4), scale(Q, 2), -1)
NJ, NO = kron(eye(2), X), kron(X, eye(2))
MJ = mul(adj(NJ), DELTA)
V = mul(adj(MJ), adj(NO))
H4 = [[F((-1)**((a&b).bit_count()), 2) for b in range(4)] for a in range(4)]


def half_flags(m, q):
    return [sum(1 << (2*i+(0 if s >> i & 1 else 1)) for i in range(m)) for s in masks(m, q)]


def lowering(m, q, weights):
    ins, outs = masks(m, q), masks(m, q-1)
    oi = {s: i for i, s in enumerate(outs)}
    out = zero(len(outs), len(ins))
    for col, s in enumerate(ins):
        for i in range(m):
            if s >> i & 1: out[oi[s ^ 1 << i]][col] = weights[i]
    return out


def primitive_cross(m, q, a, b):
    ein, cin = half_flags(m, q-1), half_flags(m, q)
    flagouts = sorted({s | 1 << (2*i) for s in ein for i in range(m) if not s >> (2*i) & 1})
    outputs = list(product(range(m), range(4), flagouts))
    oi = {v: i for i, v in enumerate(outputs)}
    matrices = []
    for xs, exceptional in [(ein, True), (cin, False)]:
        inputs = list(product(range(4), xs))
        out = zero(len(outputs), len(inputs))
        coeff = MJ if exceptional else adj(NO)
        for col, (h, s) in enumerate(inputs):
            for i in range(m):
                label = 2*i+(0 if exceptional else 1)
                if s >> label & 1: continue
                for hh in range(4):
                    out[oi[i, hh, s | 1 << label]][col] += (a[i] if exceptional else b[i])*coeff[hh][h]
        matrices.append(out)
    return mul(adj(matrices[0]), matrices[1])


def primitive_checks():
    eq(mul(V, adj(V)), eye(4))
    eq(mul(mul(NJ, Q), adj(NJ)), add(eye(4), Q, -1))
    eq(mul(mul(NO, Q), adj(NO)), Q)
    cases = []
    for m in [2, 4]:
        a = [F(3, 5)]*m
        b = [F((-1)**i*4, 5) for i in range(m)]
        weights = [x*y for x, y in zip(a, b)]
        for q in range(1, m+1):
            D = lowering(m, q, weights)
            eq(primitive_cross(m, q, a, b), kron(V, D))
            exact = F(144, 625)*q*(m-q+1)
            psd(add(scale(eye(len(D[0])), exact), gram(D), -1))
            witness = [[F((-1)**sum(i for i in range(m) if s >> i & 1))] for s in masks(m, q)]
            eq(gram(mul(D, witness)), scale(gram(witness), exact))
            cases.append({'half_rungs': m, 'q': q, 'exact_squared_norm': str(exact)})
    weights = [F(12, 25), F(-60, 169), F(120, 289), F(12, 25)]
    for q in range(1, 5):
        D = lowering(4, q, weights)
        allowance = min(q, 5-q)*sum(x*x for x in weights)
        psd(add(scale(eye(len(D[0])), allowance), gram(D), -1))
    return cases


def child(label, s, rows):
    ins = list(product(rows, masks(4, s)))
    outs = masks(4, s+1)
    oi = {x: i for i, x in enumerate(outs)}
    out = zero(len(outs), len(ins))
    for col, (j, y) in enumerate(ins):
        for a in range(4):
            if not y >> a & 1: out[oi[y | 1 << a]][col] += H4[j][a]*H4[a][label]
    return out


def consumed_cross(s, rows):
    a, b, q = [F(3, 5)]*2, [F(4, 5), F(-4, 5)], 1
    ein, cin = half_flags(2, 0), half_flags(2, 1)
    # Direct assembly and lowering use the same original half-rung ordering.
    flagouts = sorted({x | 1 << (2*i) for x in ein for i in range(2)})
    ys, yo = masks(4, s), masks(4, s+1)
    outputs = list(product(range(2), range(4), flagouts, yo))
    oi = {v: i for i, v in enumerate(outputs)}
    matrices = []
    for xs, exceptional in [(ein, True), (cin, False)]:
        inputs = list(product(range(4), xs, rows, ys))
        out = zero(len(outputs), len(inputs))
        mark = MJ if exceptional else adj(NO)
        for col, (h, x, row, y) in enumerate(inputs):
            for i in range(2):
                label = 2*i+(0 if exceptional else 1)
                if x >> label & 1: continue
                for cc in range(4):
                    if y >> cc & 1: continue
                    for hh in range(4):
                        out[oi[i, hh, x | 1 << label, y | 1 << cc]][col] += (
                            (a[i] if exceptional else b[i])*mark[hh][h]*H4[row][cc]*H4[cc][label])
        matrices.append(out)
    K = mul(adj(matrices[0]), matrices[1])
    Z = [mul(adj(child(2*i, s, rows)), child(2*i+1, s, rows)) for i in range(2)]
    expected = zero(len(K), len(K[0]))
    for i in range(2):
        weights = [F(0), F(0)]
        weights[i] = a[i]*b[i]
        expected = add(expected, kron(V, kron(lowering(2, 1, weights), Z[i])))
    eq(K, expected)
    allowance = F((s+1)**2, 16)*F(288, 625)
    psd(add(scale(eye(len(K[0])), allowance), gram(K), -1))
    if s == 0 and rows == list(range(4)):
        D = lowering(2, 1, [F(12, 25), F(-12, 25)])
        # Walsh rung phases are identical here, yielding the exact Gram.
        eq(gram(K), kron(eye(4), kron(scale(gram(D), F(1, 16)), eye(4))))
        Acycle = mul(adj(Z[1]), Z[0])
        eq(Acycle, scale(eye(4), F(1, 16)))
        omega = F(-144, 625)
        cycle = [[F(0), omega], [omega, F(0)]]
        actual_cycle = kron(cycle, Acycle)
        eq(mul(actual_cycle, actual_cycle), scale(eye(8), omega*omega/F(256)))
    return {'s': s, 'rows': rows, 'cross_squared_allowance': str(allowance)}


def pair_child(b, a):
    out = zero(6, 16)
    oo = {s: i for i, s in enumerate(masks(4, 2))}
    for j2, j1, u, v in product(range(4), repeat=4):
        if u != v:
            out[oo[(1 << u) | (1 << v)]][4*j2+j1] += H4[j1][u]*H4[u][a]*H4[j2][v]*H4[v][b]
    return out


def pair_checks():
    g = [F(3, 5), F(4, 5), F(3, 5), F(-4, 5)]
    mark = [NJ, NO, NJ, NO]
    match = [(1 << 0) | (1 << 3), (1 << 1) | (1 << 2)]
    ys = masks(4, 2)
    yi = {s: i for i, s in enumerate(ys)}
    inputs = list(product(range(4), range(2), range(4), range(4)))
    R = zero(24, len(inputs))
    # Direct original ordered edge/child path assembly of the two-stage
    # commutator, followed by ordered coefficient output e1 tensor e0.
    for col, (h, z, j2, j1) in enumerate(inputs):
        S = match[z]
        for i, l in product(range(4), repeat=2):
            if S >> i & 1 or (S | 1 << i) >> l & 1: continue
            if i//2 != 0 or l//2 != 1: continue
            word = mul(adj(mark[l]), adj(mark[i]))
            residual = add(mul(Q, word), mul(word, Q), -1)
            for u, v in product(range(4), repeat=2):
                if u == v: continue
                coefficient = g[i]*g[l]*H4[j1][u]*H4[u][i]*H4[j2][v]*H4[v][l]
                for hh in range(4):
                    R[6*hh+yi[(1 << u) | (1 << v)]][col] += coefficient*residual[hh][h]
    d0, d1 = g[1]*g[2], g[0]*g[3]
    U = mul(adj(mul(NJ, NO)), DELTA)
    F21, F30 = pair_child(2, 1), pair_child(3, 0)
    eq(R, kron(U, hstack(scale(F21, d0), scale(F30, d1))))
    Ieq = zero(16, 4)
    for j in range(4): Ieq[5*j][j] = F(1)
    H21, H30 = mul(F21, Ieq), mul(F30, Ieq)
    eq(H21, scale(H30, -1))
    HG = gram(H30)
    psd(add(scale(eye(4), F(1, 8)), HG, -1))
    w = [[F((-1)**((3&j).bit_count()))] for j in range(4)]
    eq(gram(mul(H30, w)), scale(gram(w), F(1, 8)))
    Req = mul(R, kron(eye(8), Ieq))
    eq(Req, kron(U, hstack(scale(H30, -d0), scale(H30, d1))))
    diag = kron([[d0*d0, F(0)], [F(0), d1*d1]], HG)
    loss = gram(hstack(scale(H30, d0), scale(H30, d1)))
    eq(gram(Req), kron(eye(4), add(scale(diag, 2), loss, -1)))
    psd(kron(eye(4), loss))
    # Legitimate matching-plus state with the exact maximizing row mode.
    witness = [[F(0)] for _ in range(32)]
    for z, j in product(range(2), range(4)): witness[4*z+j][0] = w[j][0]
    eq(gram(mul(Req, witness)), scale(gram(witness), F(36, 625)))
    primitive = kron(U, [[d0, d1]])
    primitive_witness = [[F(1)], [F(1)]]+[[F(0)] for _ in range(6)]
    eq(mul(primitive, primitive_witness), zero(4, 1))
    control(any(x for row in mul(Req, witness) for x in row))
    return {'original_labels': ['j0', 'o0', 'j1', 'o1'],
            'row_equality': 'actual |j> -> |j,j>', 'child_pair_relation': 'H21=-H30',
            'child_pair_squared_norm': '1/8', 'primitive_matching_plus': '0',
            'consumed_matching_plus_squared_norm': '36/625'}


def main():
    primitive = primitive_checks()
    consumed = [consumed_cross(0, list(range(4))), consumed_cross(1, list(range(4))),
                consumed_cross(1, [0, 2])]
    pair = pair_checks()
    report = {'status': 'PASS', 'arithmetic': 'exact fractions and exact Schur positivity',
              'counts': dict(COUNT), 'primitive_cases': primitive, 'consumed_cases': consumed,
              'two_creation_row_equality': pair,
              'scope': 'Real rational supplied marks and Walsh4; no sampling of general complex transforms, no sign-law enumeration.',
              'files': {str(p.relative_to(HERE.parent)): sha256(p.read_bytes()).hexdigest() for p in
                        [HERE/'cycle_transfer.md', Path(__file__).resolve(), HELPER]}}
    (HERE/'cycle_transfer_checks.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'status': 'PASS', 'counts': dict(COUNT)}))


if __name__ == '__main__': main()
