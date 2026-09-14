# A simple original cycle retains two orthogonal occupation patterns

Date: 2026-09-13. Status: analytic derivation; bounded exact checks and
independent review are recorded separately. This note controls an actual
ordered cycle term, not the sum of all cycles or the MI-32 endpoint.

## 1. The original flag product around a cycle

Use the hard-core occupation space on the original independent edge
labels. For a label e, let d_e^+ add e when it is absent and vanish
otherwise; put d_e^-=(d_e^+)* and n_e=d_e^+d_e^-.
Distinct original labels commute, while

    d_e^-d_e^+=I-n_e,   d_e^+d_e^-=n_e,
    (d_e^+)^2=(d_e^-)^2=0.                               (1)

Let a closed current-vertex path visit a simple bipartite cycle of length
2ell. Alternate a grade-k creation and a grade-(k+1) annihilation along
its successive original edges. Each cycle edge occurs once. Write E_+
for its ell creation edges and E_- for its ell annihilation edges. The
ordered flag part is exactly

    W = product_(e in E_+) d_e^+
          product_(f in E_-) d_f^- .                     (2)

The factors commute here only because these are distinct original
labels. Define the two original occupation projections

    P_- = product_(e in E_+) (I-n_e) product_(f in E_-) n_f,
    P_+ = product_(e in E_+) n_e product_(f in E_-) (I-n_f).

Every flag outside the cycle is a spectator. Direct action on an
occupation basis gives

    W*W=P_-,   WW*=P_+,   P_-P_+=0,   W^2=0.             (3)

Thus W transports the occupied alternating half of the cycle to its
complementary half, with the entire spectator set unchanged. Merely
remembering the final current vertex would erase that change.

At total grade k<ell, both projections and W vanish. At k>=ell they
are nonzero only when enough spectator labels are available. On a
raw grade where they are nonzero, W is a partial isometry with norm one.
Actual reachable-state masks can remove either pattern; their compressed
operators retain the masks and need not attain the raw norm.

## 2. Exact Hermitian contraction, including an ordered coefficient word

Factor the original occupation space into spectator and cycle registers.
Absorb the spectator register once into the retained auxiliary Hilbert
space, and in this section let W denote its cycle-register factor.
Let A be a bounded operator on that retained auxiliary space. It may be
an ordered product of noncommuting coefficient and spectator operators,
but it acts independently of the cycle flags. The norm equalities below
concern this uncompressed tensor block. At a fixed total grade k, use
the spectator grade k-ell; A must preserve that sector, and its norm
means the norm on that actual sector. A further grade or reachability
mask requires its actual compression and does not inherit norm equality.
Put

    Z=A tensor W,            H=Z+Z*.

By (3),

    Z^2=0,
    H^2=A*A tensor P_- + AA* tensor P_+,
    ||H||=||A||,          w(Z)=||A||/2,                   (4)

when the two cycle patterns are available. Here w is numerical radius.
The first norm equality follows by viewing H on the two orthogonal
patterns as the off-diagonal block matrix with A and A*. The numerical
radius follows by choosing a phase on one pattern; every rotated
Hermitian part has norm ||A||/2. No spectral theorem for the enormous
occupation space needs to be evaluated.

The exact positive upper boundary is

    H <= |H|
      = (A*A)^(1/2) tensor P_- + (AA*)^(1/2) tensor P_+.   (5)

A version avoiding square roots keeps the coefficient Gram. For t>0,

    H <= t A*A tensor P_- + t^-1 I tensor P_+,             (6)

and the difference is D*D with

    D=sqrt(t) A tensor W - t^-1/2 I tensor P_+.

Indeed P_+W=W and W*P_+=W*, so the two cross terms are precisely -H.
For a scalar coefficient a, the particularly transparent identity is

    |a|(P_-+P_+) - (aW+conj(a)W*) >= 0.                  (7)

Equation (4) improves the separate-term triangle allowance 2||A|| by
a factor two for this Hermitian cycle. It is not an improvement for an
arbitrary sum of overlapping cycles: those terms can share occupation
patterns and must be assembled through their actual Gram. Equations
(5)--(7), rather than only that factor, are the retained interface.

## 3. The first square and its actual continuation

For the square with rows r0,r1 and columns c0,c1, name the original
edges e_t=(r0,c_t), f_t=(r1,c_t), t=0,1. The nontrivial return path
between grade-two inputs is

    (r1,{e0,f1}) -> (c0,{e0,f0,f1}) -> (r0,{f0,f1})
                 -> (c1,{e1,f0,f1}) -> (r1,{e1,f0}).     (8)

Every indicated output has occupied degree two. The invariant
boundary(S) symmetric-difference {current vertex} is the same along
the path. The first and last inputs have the same current vertex and
different original occupations. With

    w_t=d_e_t^- d_f_t^+,
    W=w_1* w_0,

the flag transport of (8) is exactly (2), from {e0,f1} to {e1,f0}.
Its scalar graph coefficient is the product of the four original edge
weights. The exact square block and its extension to interacting
two-column rungs are derived in the companion geometry note.

The companion original-model transfer identifies this same product
inside the primitive marked Parseval cross and the actual consumed-SRHT
cross. In the consumed map the retained auxiliary coefficient is the
ordered row product D_1*D_0, with D_t=L_e_t*L_f_t. Equation (6) retains
its actual Gram rather than treating it as an independent row copy.
The precise supplied marks and flatness assumptions belong to that
derivation; no full sampling theorem is claimed here.

## 4. What survives extension and identification

Appending a bounded operator B on retained auxiliary/spectator spaces
updates A to the actual ordered product AB or BA. If the cycle labels
are still disjoint from those factors, (3)--(6) remain valid with that
updated product. There is no need for A and B to commute.

For any common input map R, including a supplied boundary identification,

    R* H R <= R* |H| R,

and the entire positive difference in (6) is transported by congruence.
This does not assert that (R* Z R)^2=0, or that its norm uses the old
scalar allowance without the actual R factors. A direct map inserting
or removing a cycle label must be evaluated with (1), retaining the
updated projections and any resulting term.

There is a concrete failure of a frozen square-zero certificate under
original-label substitution. Apply the identification e0=f0=x and
e1=f1=y to the sequential word W=w_1* w_0 above. The rederived word is

    d_y^- d_y^+ d_x^- d_x^+ = (I-n_y)(I-n_x),             (9)

which is the nonzero projection onto the identified two-flag vacuum.
Its square equals itself and its numerical radius is one, rather than
one half. This is fresh evaluation of the specified sequential
creation/annihilation word; it does not preserve the original grade-two
restriction. It is not an assertion that original
Rademacher variable identification preserves a creation-only sector:
the full multiplication rule additionally uses epsilon_x^2=1 and can
generate different grade channels. Sequential creator substitution is
not a homomorphism of the old independent hard-core algebra: for e!=f,
d_e^-d_f^+=d_f^+d_e^- originally, whereas identifying e=f=x in those two
expressions gives I-n_x and n_x, respectively. Its given chronological
word must therefore be evaluated afresh in the new flag algebra. The
full Rademacher multiplication algebra instead has its actual parity
quotient. Neither operation is a free relabeling of this old budget.

Even before any identification, composing two different simple-cycle
words may produce a nonzero product. Individual W_c^2=0 is not a rule
that W_c W_d=0, nor a bound for arbitrary sums. The collective adjacent
occupation layers of the two-column family provide a concrete next
assembly problem; a fixed current-vertex scalar erases those layers.

## 5. Comparison, scope and cost

The abstract numerical-radius statement is established operator theory.
The square-zero case is the elementary sharp case of
[Haagerup--de la Harpe, Theorem 1, 1992](https://access.archive-ouverte.unige.ch/access/metadata/2e3d55fc-f7d2-42af-95ae-6c06df864dbb/download).
The elementary proof above is included to expose the original occupation
projections and the coefficient Gram needed after an interaction. No
novelty claim is made for nilpotent operators or positive block budgets.

This note advances the analytic ambition only through an exact simple
cycle term and its actual transfer. It does not control all short
cycles in an arbitrary heavy support, infer a sharp full-law moment
bound, or establish a norm quantile. The full-law even-cycle excursion
calculation is distinct: it retains every entry's multiplicity rather
than treating (2) as an even-moment scalar identity.

Recognizing the specified simple cycle and its two alternating label
sets takes O(ell) label operations. Applying the occupation test requires
those original label bits and the spectator record. Computing or bounding
the ordered coefficient Gram, its square root in (5), arbitrary boundary
maps, state size and bit growth have their separate costs. The proof
does not require explicit enumeration of the occupation space.
