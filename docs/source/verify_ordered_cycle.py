"""Bounded exact checks for the retained original-cycle boundary.

Uses the frozen sparse rational matrix helper without running its suite.
No random-law sampling and no numerical spectra are used.
"""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import json
import runpy

HERE=Path(__file__).resolve().parent
HELPER=HERE.parent/'mi32_exchange_2026-09-13'/'verify_heavy_light_cross.py'
base=runpy.run_path(str(HELPER))
Mat,ident,diag,gram,eq,psd,nonzero,creator,edge_states=(base[k] for k in
    ['Mat','ident','diag','gram','eq','psd','nonzero','creator','edge_states'])


def kron(a,b):
    return Mat(a.n*b.n,a.m*b.m,{(i*b.n+k,j*b.m+l):x*y
        for (i,j),x in a.a.items() for (k,l),y in b.a.items()})


def action(states,operations):
    index={s:j for j,s in enumerate(states)}
    out={}
    for j,s in enumerate(states):
        t=set(s)
        for label,up in operations:
            if (up and label in t) or (not up and label not in t):
                break
            if up:t.add(label)
            else:t.remove(label)
        else:
            if frozenset(t) in index:
                out[index[frozenset(t)],j]=1
    return Mat(len(states),len(states),out)


def main():
    cases=[]
    a=Mat(2,2,{(0,0):1,(0,1):F(2,3),(1,0):-1,(1,1):F(1,2)})
    for ell in (2,3):
        n=2*ell+1  # one real spectator flag, retained in every formula
        adds=set(range(0,2*ell,2))
        removes=set(range(1,2*ell,2))
        operations=[(e,e in adds) for e in range(2*ell)]
        for k in range(n+1):
            states=[frozenset(s) for s in combinations(range(n),k)]
            w=action(states,operations)
            pminus=diag([int(removes<=s and not(adds&s)) for s in states])
            pplus=diag([int(adds<=s and not(removes&s)) for s in states])
            zero=Mat(len(states),len(states))
            eq(w@w,zero,'square-zero cycle word')
            eq(gram(w),pminus,'actual initial occupation projection')
            eq(w@w.t(),pplus,'actual final occupation projection')
            eq(pminus@pplus,zero,'orthogonal cycle patterns')
            z=kron(a,w)
            h=z+z.t()
            expected=kron(gram(a),pminus)+kron(a@a.t(),pplus)
            eq(h@h,expected,'Hermitian cycle squared identity')
            for t in (F(1,2),F(1),F(3)):
                allowance=kron(gram(a).scale(t),pminus)+kron(ident(2,F(1,t)),pplus)
                # Avoid irrational sqrt(t): t times the difference is one Gram.
                difference=z.scale(t)-kron(ident(2),pplus)
                eq((allowance-h).scale(t),gram(difference),'retained ordered coefficient square')
                psd(allowance-h,'positive cycle boundary')
            cases.append({'cycle_length':2*ell,'grade':k,'states':len(states),'nonzero':bool(w.a)})
    # Actual closed current-vertex path on the original signed square.
    edges=[(0,2),(0,3),(1,2),(1,3),(4,5)]
    weights=[F(1),F(-1,2),F(2,3),F(3,4),F(1)]
    beta=weights[0]*weights[1]*weights[2]*weights[3]
    for k in (2,3):
        ins,outs=edge_states(6,5,k),edge_states(6,5,k+1)
        maps=[creator(edges,weights,{e},ins,outs) for e in range(4)]
        actual=maps[3].t()@maps[1]@maps[0].t()@maps[2]
        index={state:i for i,state in enumerate(ins)}
        entries={}
        for j,(v,s) in enumerate(ins):
            if v==1 and {0,3}<=s and not ({1,2}&s):
                entries[index[(1,(s-{0,3})|{1,2})],j]=beta
        eq(actual,Mat(len(ins),len(ins),entries),'actual original signed square path')
        nonzero(actual,'available square path with spectator grade')
    # Re-derive the sequential word after explicit label substitution.
    states=[frozenset(s) for k in range(3) for s in combinations(range(2),k)]
    substituted=action(states,[(0,True),(0,False),(1,True),(1,False)])
    empty=diag([int(not s) for s in states])
    eq(substituted,empty,'identified sequential word is empty-pattern projection')
    eq(substituted@substituted,substituted,'identified word is idempotent')
    nonzero(substituted,'identification destroys square-zero property')
    # Explicit norm-one Hermitian word witness, no floating square roots.
    states=[frozenset(s) for s in combinations(range(4),2)]
    w=action(states,[(2,True),(0,False),(1,True),(3,False)])
    h=w+w.t()
    vec=Mat(len(states),1,{(states.index(frozenset({0,3})),0):1,
                           (states.index(frozenset({1,2})),0):1})
    eq(h@vec,vec,'attained Hermitian cycle norm one')
    eq(vec.t()@w@vec,Mat(1,1,{(0,0):1}),'numerical radius half on norm-squared-two witness')
    report={'status':'PASS','arithmetic':'exact fractions.Fraction and integer occupation masks',
            'cases':cases,'matrix_checks':dict(base['COUNTS']),
            'actual_square_grades':[2,3],
            'dependencies':[{'path':str(p),'sha256':sha256(p.read_bytes()).hexdigest()}
                            for p in [Path(__file__),HERE/'ordered_cycle_boundary.md',HELPER]],
            'limits':['Only cycle lengths four and six with one spectator are enumerated.',
                      'The coefficient fixture is real rational and nonnormal; complex formulas are proved analytically.',
                      'Identification is a specified sequential creation-word substitution, not the full sign-law quotient.',
                      'No claim about all-cycle assembly, actual norm moments, quantiles or MI-32.']}
    (HERE/'ordered_cycle_checks.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'PASS','cases':len(cases),'matrix_checks':report['matrix_checks']}))


if __name__=='__main__':main()
