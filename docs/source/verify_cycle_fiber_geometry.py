"""Exact bounded checks of original-edge cycle-fiber Gram formulas."""
from collections import defaultdict, Counter
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
from hashlib import sha256
import json

HERE = Path(__file__).resolve().parent


def masks(n, k):
    for c in combinations(range(n), k):
        yield sum(1 << i for i in c)


def bd(edges, s):
    out = 0
    for e, (u, v) in enumerate(edges):
        if s >> e & 1:
            out ^= (1 << u) | (1 << v)
    return out


def add(a, i, j, value):
    a[i, j] += value
    if not a[i, j]:
        del a[i, j]


def gram_from_rows(rows):
    out = defaultdict(F)
    for entries in rows.values():
        for i, x in entries:
            for j, y in entries:
                add(out, i, j, x*y)
    return dict(out)


def creator(edges, weights, a, k):
    by_input, by_output = defaultdict(list), defaultdict(list)
    for s in masks(len(edges), k):
        for v in range(a+2):
            for e, (u, w) in enumerate(edges):
                if s >> e & 1 or v not in (u, w):
                    continue
                z = w if v == u else u
                t = s | (1 << e)
                if sum(bool(t >> f & 1) for f, edge in enumerate(edges) if z in edge) < 2:
                    continue
                inp, out = (v, s), (z, t)
                by_input[inp].append((out, weights[e]))
                by_output[out].append((inp, weights[e]))
    return by_input, by_output


def rung_sets(a, s):
    half, full, orientation = set(), set(), {}
    for i in range(a):
        bits = (s >> (2*i)) & 3
        if bits == 3:
            full.add(i)
        elif bits:
            half.add(i)
            orientation[i] = 0 if bits == 1 else 1
    return half, full, orientation


def graph_components(by_input, by_output):
    adj = defaultdict(list)
    for inp, entries in by_input.items():
        for out, _ in entries:
            x, y = (0, *inp), (1, *out)
            adj[x].append(y)
            adj[y].append(x)
    seen = set()
    for seed in adj:
        if seed in seen:
            continue
        todo, comp = [seed], []
        seen.add(seed)
        while todo:
            x = todo.pop()
            comp.append(x)
            for y in adj[x]:
                if y not in seen:
                    seen.add(y)
                    todo.append(y)
        yield comp, adj


def verify_arbitrary_count_blocks():
    """Independently rebuild full creator factors on actual selected rows/columns."""
    edges = [(0,3),(0,4),(0,6),(1,3),(1,4),(1,5),(2,4),(2,5),(2,6)]
    weights = [F(1),F(-2),F(1,3),F(3,2),F(-1,2),F(2,3),F(-3),F(1,4),F(4,3)]
    nleft,nv = 3,7
    counts = Counter()
    def maps(selected,vertices,k):
        # Enumerate local flags, then embed by the actual original edge IDs.
        by_in,by_out = defaultdict(list),defaultdict(list)
        for local in masks(len(selected),k):
            s=sum(1<<e for j,e in enumerate(selected) if local>>j&1)
            for v in vertices:
                for e in selected:
                    u,w=edges[e]
                    if s>>e&1 or v not in (u,w):
                        continue
                    z=w if v==u else u
                    inp,out=(v,s),(z,s|(1<<e))
                    by_in[inp].append((out,weights[e]))
                    by_out[out].append((inp,weights[e]))
        return by_in,by_out
    def profile(out):
        v,s=out
        if v>=nleft:
            return ('rows',tuple(sum(bool(s>>e&1) for e,(i,j) in enumerate(edges) if i==r)
                                 for r in range(nleft)))
        return ('cols',tuple(sum(bool(s>>e&1) for e,(i,j) in enumerate(edges) if j==c)
                             for c in range(nleft,nv)))
    cases=[]
    for k in range(5):
        by_in,by_out=maps(list(range(len(edges))),range(nv),k)
        for entries in by_in.values():
            for x,_ in entries:
                for y,_ in entries:
                    assert profile(x)==profile(y)
                    counts['shared_predecessor_count_invariance']+=1
        groups=defaultdict(set)
        for out in by_out:
            groups[profile(out)].add(out)
        cache={}
        for (side,d),outs in groups.items():
            selected_axis=frozenset(i for i,x in enumerate(d) if x)
            assert len(selected_axis)<=k+1
            counts['occupied_axis_support_size']+=1
            key=(side,selected_axis)
            if key not in cache:
                if side=='rows':
                    chosen=[e for e,(i,j) in enumerate(edges) if i in selected_axis]
                    vertices=set(selected_axis)|set(range(nleft,nv))
                else:
                    chosen=[e for e,(i,j) in enumerate(edges) if j-nleft in selected_axis]
                    vertices=set(range(nleft))|{j+nleft for j in selected_axis}
                cache[key]=maps(chosen,vertices,k)[1]
            local_out=cache[key]
            selected_outs={out for out in local_out if profile(out)==(side,d)}
            assert selected_outs==outs
            counts['exact_count_block_output_sets']+=1
            for out in outs:
                assert dict(local_out[out])==dict(by_out[out])
                counts['exact_selected_submatrix_factor_rows']+=1
        cases.append({'grade':k,'full_input_states_with_transitions':len(by_in),
                      'full_output_states_with_transitions':len(by_out),'count_blocks':len(groups)})
    return {'support':'signed unequal 3-by-4, nine original nonzero entries',
            'counts':dict(counts),'cases':cases,
            'scope':'Full creators and exact original-edge submatrix factor masks; no hypercontractive or moment endpoint is tested.'}


def verify_parseval_count_insertion():
    results=[]
    for a in range(2,6):
        # All-positive K_(a,2), original vacuum row inputs and distinct edge outputs.
        outputs=[(a+t,1<<(2*i+t)) for i in range(a) for t in range(2)]
        coeff={out:[F(int(i==j)) for j in range(a)]
               for i in range(a) for out in outputs[2*i:2*i+2]}
        row_gram=[[F(1,a) for _ in range(a)] for _ in range(a)]
        Q=[[sum(coeff[x][i]*row_gram[i][j]*coeff[y][j]
                for i in range(a) for j in range(a)) for y in outputs] for x in outputs]
        original=[[sum(coeff[x][i]*coeff[y][i] for i in range(a)) for y in outputs] for x in outputs]
        pinched=[[Q[i][j] if i//2==j//2 else F(0) for j in range(2*a)] for i in range(2*a)]
        assert Q==[[F(1,a) for _ in outputs] for _ in outputs]
        assert all(sum(row)==2 for row in Q)
        assert all(sum(row)==F(2,a) for row in pinched)
        # Exact positive loss: original-Q=(1/a)sum_(i<j)(v_i-v_j)(v_i-v_j)*.
        loss=[[F(0) for _ in outputs] for _ in outputs]
        for i,j in combinations(range(a),2):
            v=[F(int(t//2==i)-int(t//2==j)) for t in range(2*a)]
            for r in range(2*a):
                for s in range(2*a):
                    loss[r][s]+=v[r]*v[s]/a
        assert loss==[[original[i][j]-Q[i][j] for j in range(2*a)] for i in range(2*a)]
        results.append({'rows':a,'actual_output_gram_norm':'2',
                        'pinched_output_gram_norm':str(F(2,a)),'exact_positive_loss':True})
    return {'cases':results,'exact_assertions':4*len(results),
            'scope':'Supplied Parseval analysis R=ones/sqrt(a) before actual matrix-unit row consumption; no automatic SRHT assertion.'}


def main():
    a = 4
    edges = [(i, a+t) for i in range(a) for t in range(2)]
    weights = [F(1), F(-2), F(3,2), F(1,2), F(-1,3), F(4,3), F(2,3), F(-3,2)]
    counts, cases = Counter(), []
    for k in range(8):
        by_input, by_output = creator(edges, weights, a, k)
        # Actual output-column return Gram, assembled through shared inputs.
        col_out = {z for z in by_output if z[0] >= a}
        col_rows = {v: [(z,b) for z,b in entries if z in col_out]
                    for v,entries in by_input.items()}
        actual_col = gram_from_rows(col_rows)
        predicted_col = defaultdict(F)
        profiles = set()
        for z in col_out:
            w, s = z
            t = w-a
            A, full, orient = rung_sets(a, s)
            eta = bd(edges, s) ^ (1 << w)
            assert {i for i in range(a) if eta >> i & 1} == A
            assert len(A)+2*len(full) == k+1
            gamma = 1 ^ ((eta >> a) & 1) ^ (len(full) & 1) ^ (len(A) & 1)
            assert t == (sum(orient.values()) & 1) ^ gamma
            counts['column_state_invariants'] += 3
            profiles.add((eta,tuple(sorted(full))))
            diagonal = sum((weights[2*i+t]**2 for i in full), F(0))
            diagonal += sum((weights[2*i+t]**2 for i in A if orient[i] == t), F(0))
            add(predicted_col,z,z,diagonal)
            for i in A:
                if orient[i] == t:
                    neighbor = (a+1-t, s ^ (3 << (2*i)))
                    if neighbor in col_out:
                        add(predicted_col,z,neighbor,weights[2*i]*weights[2*i+1])
        assert actual_col == dict(predicted_col)
        counts['exact_global_gram_equalities'] += 1
        # Actual return-output-row input Gram, assembled through shared outputs.
        row_out_rows = {z: entries for z,entries in by_output.items() if z[0] < a}
        actual_row = gram_from_rows(row_out_rows)
        predicted_row = defaultdict(F)
        for s in masks(2*a,k):
            A, full, orient = rung_sets(a,s)
            for t in range(2):
                v = (a+t,s)
                opposite = [i for i in A if orient[i] != t]
                diagonal = sum((weights[2*i+t]**2 for i in opposite), F(0))
                add(predicted_row,v,v,diagonal)
                for i in opposite:
                    neighbor = (a+1-t, s ^ (3 << (2*i)))
                    add(predicted_row,v,neighbor,weights[2*i]*weights[2*i+1])
        assert actual_row == dict(predicted_row)
        counts['exact_global_gram_equalities'] += 1
        if k == 2:
            classes = Counter()
            for comp, adj in graph_components(by_input,by_output):
                etas = {bd(edges,z[2]) ^ (1 << z[1]) for z in comp}
                assert len(etas) == 1
                eta = next(iter(etas))
                size = eta.bit_count()
                ins = [z for z in comp if z[0] == 0]
                outs = [z for z in comp if z[0] == 1]
                if size == 3:
                    side_sizes = (sum(bool(eta >> i & 1) for i in range(a)),
                                  sum(bool(eta >> i & 1) for i in (a,a+1)))
                    if 0 in side_sizes:
                        assert len(ins)==3 and len(outs)==1
                        classes['three_star'] += 1
                    else:
                        assert len(ins)==3 and len(outs)==2
                        assert sorted(len(adj[z]) for z in ins)==[1,1,2]
                        assert all(len(adj[z])==2 for z in outs)
                        classes['active_square_path'] += 1
                elif size == 5:
                    assert len(ins)==len(outs)==6
                    assert all(len(adj[z])==2 for z in comp)
                    classes['three_rung_cycle_12'] += 1
                else:
                    raise AssertionError(('unexpected eta return sector',size))
                counts['grade_two_component_classifications'] += 1
            grade_two_classes = dict(classes)
        cases.append({'grade':k,'return_inputs':len(by_input),'return_outputs':len(by_output),
                      'column_profiles':len(profiles)})
    # Inclusion matrices: exact constant-vector singular equations, not numerical spectra.
    for n in range(1,8):
        for r in range(n):
            lower, upper = list(combinations(range(n),r)), list(combinations(range(n),r+1))
            d0,d1 = n-r,r+1
            assert all(sum(set(x)<set(y) for y in upper)==d0 for x in lower)
            assert all(sum(set(x)<set(y) for x in lower)==d1 for y in upper)
            for f in range(4):
                # Top eigenvalue f+n+1 follows from the exact 2-by-2 characteristic identity.
                lam=f+n+1
                assert (lam-(f+d0))*(lam-(f+d1))==d0*d1
                counts['equal_rung_characteristic_identities'] += 1
    # All-positive occupied-square projection: unnormalized (1,-1) gives energies 2 and 0.
    Q = [[F(2),F(1)],[F(1),F(2)]]
    folded = [[F(2),F(2)],[F(2),F(2)]]
    y = [F(1),F(-1)]
    assert sum(y[i]*Q[i][j]*y[j] for i in range(2) for j in range(2)) == 2
    assert sum(y[i]*folded[i][j]*y[j] for i in range(2) for j in range(2)) == 0
    counts['positive_square_projection_checks'] = 2
    # Positive weighted square: uniform normalized occupation fold misses the full top norm.
    weighted_Q = [[F(2),F(2)],[F(2),F(5)]]
    top = [F(1),F(2)]
    assert [sum(weighted_Q[i][j]*top[j] for j in range(2)) for i in range(2)] == [6*x for x in top]
    uniform_Q = [[F(3,2),F(5,2)],[F(5,2),F(9,2)]]
    assert 6-uniform_Q[0][0] > 0
    assert (6-uniform_Q[0][0])*(6-uniform_Q[1][1])-uniform_Q[0][1]**2 == F(1,2)
    counts['weighted_uniform_fold_checks'] = 3
    arbitrary_count_blocks=verify_arbitrary_count_blocks()
    parseval_insertion=verify_parseval_count_insertion()
    report={'status':'PASS','arithmetic':'exact integers and fractions.Fraction',
            'counts':dict(counts),'cases':cases,'grade_two_classes':grade_two_classes,
            'arbitrary_count_blocks':arbitrary_count_blocks,
            'parseval_count_insertion':parseval_insertion,
            'dependencies':{name:sha256((HERE/name).read_bytes()).hexdigest()
                            for name in [Path(__file__).name,'cycle_fiber_geometry.md'] if (HERE/name).exists()},
            'limits':['Exact finite evidence for weighted K_(4,2), eight grades, and inclusion identities through n=7.',
                      'No floating-point eigenvalues, no R_B supremum evaluation, no enumeration of random signs.',
                      'The uniform Gram, local-support, weak-moment, and folding claims are proved analytically in the note.',
                      'Raw eta sectors are not asserted to share one root; the note distinguishes actual root reachability.']}
    (HERE/'cycle_fiber_geometry_checks.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'PASS','counts':dict(counts),'grade_two_classes':grade_two_classes,
                      'arbitrary_count_blocks':arbitrary_count_blocks['counts']},indent=2))


if __name__=='__main__':
    main()
