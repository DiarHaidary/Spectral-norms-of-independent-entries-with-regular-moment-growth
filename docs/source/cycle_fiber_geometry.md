# Original cycle fibers: a positive difference channel and an all-grade rung Gram

Date: 2026-09-13. Status: self-contained analytic derivations, with bounded
exact checks scoped in Section 8. This continues the same MI-32 creator
and weak-moment frontier. It does not solve the unrestricted sign problem
or the full regular-law conjecture, and makes no novelty claim.

The main object is the exact occupied-fiber Gram on a weighted K_(a,2).
It contains many interacting four-cycles without a feedback-edge count.
Its repeated original vertices can be folded only if the lost occupation
difference channels remain in the positive boundary. The all-positive
square already separates a scalar norm comparison from a budget that
survives the next common output contraction.

## 1. Original states and exact grade-two return templates

Let G be a finite simple bipartite support graph with real nonzero
coefficients b_e on its original edges. Independent entry signs remain
attached to these edges. On the raw basis (v,S), |S|=k, let

    C_k |v,S> = sum_(e=vw absent from S) b_e |w,S union {e}>.

The return creator keeps outputs (w,T) with deg_T(w)>=2. Its invariant is

    eta = boundary(S) symmetric-difference {v}.

This is a parity label, not an assertion of root reachability. At grade
two every return output has three occupied edges. Its component is one
of a three-star, a three-edge path with current vertex internal, or a
two-star plus a disjoint edge. Thus its eta has size three or five;
there is no singleton-eta return output. In particular, the two
length-two paths across a four-cycle give distinct input occupations at
the same original current vertex and the same singleton eta, but the
grade-two return creator vanishes on that entire singleton sector.

Here is the complete grade-two return classification. Transpose rows and
columns where appropriate. Absent original edges retain availability
masks; the resulting maps are the corresponding template compressions.

* If eta consists of three vertices on the same bipartite side, each
  common neighbor w gives one independent return output, with the three
  possible newly created edges as predecessors. Its matrix is the
  one-row coefficient vector (b_(a,w),b_(b,w),b_(c,w)). Different w have
  different occupations and belong to different return components.
* If eta={r0,c0,c1}, for each common row neighbor r distinct from r0 set
  a_t=b_(r0,ct) and x_t=b_(r,ct). The three inputs are

      A_r  = (r0,{r c0,r c1}),
      B_r0 = (r, {r0 c0,r c1}),
      B_r1 = (r, {r0 c1,r c0}).

  The two outputs are Y_rt=(ct,{r0 ct,r c0,r c1}). The exact matrix is

      M_r = [ a0  x0   0 ]
            [ a1   0  x1 ].                                  (1)

  With all four edges present its transition component is a five-vertex
  path. In particular B_r0 and B_r1 have the same original current
  vertex and distinct original occupations. Different r give a direct
  sum. This identifies the first active repeated-vertex square.
* If eta has five vertices, it must have bipartition sizes two and
  three. Inputs are the six possible assignments of one of the three
  vertices as current vertex and a matching from the other two to the
  opposite pair. Outputs assign the three occupied edges to the pair
  with degrees two and one, with current vertex the degree-two member.
  On a full K_(2,3), the return transition graph is a twelve-cycle with
  six inputs and six outputs: each input creates one of two absent
  edges, and each output has two predecessors. It uses six original
  edges. Missing original edges give the actual masked subgraphs.

These templates exhaust the three possible three-edge output shapes.
They keep the original edge labels, including repeated appearances of
one coefficient. In particular, the active square and the twelve-cycle
are raw eta sectors of sizes three and five; they are not falsely
declared reachable from one vacuum root. Later genuinely reachable
states are addressed below.

## 2. Absolute-coefficient folding loses a positive occupation channel

For the all-positive unit square, (1) gives

    M M* = [2 1],          B B* = [2 2],
           [1 2]                  [2 2]
    where B = [1 1; 1 1]

is the matrix obtained by folding the two r-current input occupations
to its one original coefficient vertex. The scalar comparison
||M||=sqrt(3)<=||B||=2 is valid. It does **not** give M M*<=B B*:
their difference is [0 1;1 0], which is indefinite.

Let L be the one-row common output contraction (1,-1)/sqrt(2). Then

    L B=0,                 ||L M||=1.                        (2)

Thus even an all-positive absolute-coefficient fold cannot serve as an
upper positive output-Gram boundary under the next contraction. This
claim concerns the actual original occupied square, not a change of
coefficient signs. The preceding phase/identification obstruction in
[the reused-boundary note](../reused_boundary_2026-09-13/second_model_transfer.md)
already shows why a generic coefficient-phase argument is insufficient;
(2) isolates an occupation difference channel without any negative
coefficient.

The exact restoration is elementary but must be applied to the actual
fiber. In (1), put c=(a0,a1), u=(x0,0), v=(0,x1). Then

    M M* = c c*
       + (1/2)(u+v)(u+v)* + (1/2)(u-v)(u-v)*.               (3)

The normalized uniform fold retains c and (u+v)/sqrt(2); the missing
column is (u-v)/sqrt(2). For any common next left map L, (3) remains an
exact equality after replacing c,u,v by Lc,Lu,Lv. More generally, for
the actual output columns a_1,...,a_m of one repeated-current input
fiber, with s=sum_j a_j,

    sum_j a_j a_j* = (1/m) s s*
       + (1/m) sum_(j<l) (a_j-a_l)(a_j-a_l)*.                (4)

This is the usual finite variance identity. Its first term is the
normalized fold; its second is the positive collection that occupation
erasure loses. A shared continuation can make the first term vanish
while preserving the second, as (2) demonstrates. No independently
resampled signs may be assigned to these difference columns.

A precise norm-preservation criterion is also available. Let J be the
isometry placing one chosen unit profile into each input fiber. Then

    C C* = C J J* C* + C(I-JJ*)C*.                            (5)

The compressed fold C J is always a contraction of C. It recovers the
full norm exactly if and only if some unit top eigenvector y of C C*
satisfies (I-JJ*)C*y=0. Merely suppressing the positive second term
gives a lower Gram, not a transportable upper budget.

For (1), choose profile (u0,u1) on its repeated r-current fiber. If
coefficients and the top output vector y are positive, the norm-
preserving choice is proportional to (x0 y0,x1 y1). A fixed uniform
profile need not work. For example, a=(1,2), x=(1,1) gives

    M M*=[2 2;2 5],       ||M||^2=6,
    (M J)(M J)*=[3/2 5/2;5/2 9/2]

for the normalized uniform fold. Its largest eigenvalue is
(6+sqrt(34))/2<6. The problem persists with strictly positive weights.
By contrast ||M||<=|| |B| || remains true: its two-by-two output Grams
have the same diagonal, while the magnitudes of their off-diagonal
entries are |a0 a1| and |a0 a1|+|x0 x1| respectively. Compare the
entrywise absolute output Gram to the nonnegative coefficient Gram.
This valid scalar comparison
does not remove the residual in (3) or (5).

## 3. The exact all-grade output-column Gram on weighted K_(a,2)

Use rows i=1,...,a, columns c0,c1, and original coefficients b_(i,t).
A rung is the pair of original edges (i,c0),(i,c1); it is empty, half
occupied with orientation s_i in {0,1}, or fully occupied. Initially
assume every coefficient is nonzero. Zero-edge and reachable-state
restrictions are applied with their genuine masks after the raw proof.

Fix an invariant eta and a grade-(k+1) output whose current vertex is a
column. Let A be the set of row vertices in eta, n=|A|. Exactly the
rungs in A are half occupied. Let F be the set of fully occupied rungs,
disjoint from A, and f=|F|. Thus

    n+2f=k+1.                                               (6)

An output is indexed by orientations s in {0,1}^A. Its current column
t=t(s) is forced by the column parity. If eta_0 records membership of
c0 in eta and m(s)=sum_i s_i, then

    t(s) = m(s) mod 2 xor gamma,
    gamma = 1 xor eta_0 xor (f mod 2) xor (n mod 2).          (7)

The second column parity is consistent because eta has odd cardinality.
This formula is a statement about an existing invariant sector, not a
license to introduce unavailable states.

For fixed eta,F, the exact full-creator output Gram Q=C_k C_k* has

    Q(s,s) = D(s)
      = sum_(i in F) b_(i,t(s))^2
        + sum_(i in A: s_i=t(s)) b_(i,t(s))^2,              (8)

and the only off-diagonal entries are

    Q(s xor {i},s)=b_(i,0)b_(i,1)
      when i in A and s_i=t(s).                            (9)

The neighbor's current column is 1-t(s). Different eta,F blocks are
orthogonal. The return output Gram is exactly P_ret Q P_ret, where

    P_ret(s)=1{ f + #{i in A:s_i=t(s)} >= 2 }.              (10)

Here is the derivation. Every occupied edge at an output gives one
predecessor, yielding (8). Two different output columns can share an
input only when its current row has an empty rung; creating either
edge gives the two half orientations of that same original rung. The
two coefficients multiply to (9), while all other flags remain fixed.
Removing one edge from a full rung instead gives an input with its
other edge occupied and only one possible creation from that row; it
contributes the full-rung diagonal in (8), with no off-diagonal term.
This proves the exact formula without a feedback-edge count or a
folding assumption.

## 4. The retained Boolean inclusion profile and exact equal-rung values

Set R={i in A:s_i=1}. The nontrivial blocks of (8)–(9) pair Hamming
layers |R|=r and |S|=r+1, where r mod 2=gamma. Their current columns are
0 and 1 respectively. There may also be isolated endpoint orientations;
their diagonal contains only full-rung energy. Write

    kappa_i=b_(i,0)b_(i,1),
    I_r(S,R)=kappa_i if S=R union {i}, and zero otherwise.

The actual paired block is

    Q_(A,F,r) = [ D_0       I_r* ] ,                        (11)
                [ I_r       D_1 ]

where

    D_0(R)=sum_(i in F)b_(i,0)^2 + sum_(i in A minus R)b_(i,0)^2,
    D_1(S)=sum_(i in F)b_(i,1)^2 + sum_(i in S)b_(i,1)^2.     (12)

Neither diagonal may be dropped when reading or transporting this
Gram. The off-diagonal is the familiar weighted Boolean inclusion
operator. A direct predecessor Cauchy inequality and its complementary-
subset version give

    ||I_r||^2 <= min(r+1,n-r) sum_(i in A)|kappa_i|^2.        (13)

For example, each upper output has r+1 predecessors. Cauchy followed
by summing the available input weights gives the factor r+1. Transpose
and take complements to obtain n-r. This is a derived scalar bound
for this particular inclusion operator, not an assertion that the
whole Gram is controlled by it alone. The exact two-step collective
cycle cross is I_r*I_r: its off-diagonal terms replace one original
half-rung orientation by another and retain both rung identities.

For equal kappa, the exact inclusion norm is

    ||I_r||^2=(r+1)(n-r)|kappa|^2.                          (14)

The constant vectors on the two levels attain this value, and row/
column Cauchy gives the matching upper bound. This is the elementary
Boolean inclusion calculation, often expressed using angular momentum;
the present contribution is recovering it at the actual creator
interface with (12) and its original flags intact.

More generally, suppose each rung has the same two positive amplitudes
b_(i,0)=alpha, b_(i,1)=beta. Uniform profiles on the two layers give
the exact top two-by-two matrix

    [ (f+n-r)alpha^2            alpha beta sqrt((r+1)(n-r)) ]
    [ alpha beta sqrt((r+1)(n-r))       (f+r+1)beta^2        ]. (15)

All entries of the full block are nonnegative, its diagonal is constant
on each layer, and the inclusion graph is connected, so the positive
constant-layer eigenvector gives its top eigenvalue. Equivalently the
same value follows from the scalar norm bound in (14) and attainment.
Thus its top eigenvalue is

    (d0+d1 + sqrt((d0-d1)^2
                   +4 alpha^2 beta^2(r+1)(n-r)))/2.

In particular, for unit coefficients it is exactly

    lambda_max(Q_(A,F,r))=f+n+1.                            (16)

The return projection keeps the lower side iff f+n-r>=2 and the upper
side iff f+r+1>=2. If both survive, (15)–(16) apply unchanged. If one
side is removed, the remaining Gram is its actual diagonal. In
particular, when f=0 the endpoint layer pairs lose their degree-one
side; the surviving diagonal is n. The twelve-cycle grade-two example
has n=3,f=0,r=1 and return norm squared four.

## 5. Return outputs at row vertices and local weak-moment support

The other direction has a similarly explicit formula and is needed for
the full return norm. Index input-column states by the same invariant
eta, its row set A, half orientations s, and spectator full set F, now
with n+2f=k. Let t(s) again be given by (7) for these input flags.
Creating a return at row i is possible precisely when i is half
occupied with s_i different from t(s); the creation completes that
same original rung. The input Gram of this row-return map has

    Q_row(s,s)=sum_(i in A:s_i different from t(s))b_(i,t(s))^2,
    Q_row(s xor {i},s)=b_(i,0)b_(i,1)
       for i in A with s_i different from t(s).             (17)

There is no full-rung diagonal in (17): those rungs are spectators for
this map. The paired layers are the complementary parity pairs to
(11). For unit coefficients, every nonzero paired block has norm
squared n+1. All these formulas are exact same-input Gram identities.

They also give an occupation-sensitive local support reduction. A
column-output block in (8) uses only original rungs A union F, numbering
n+f<=k+1. Every predecessor of its outputs is already supported on those
rungs. Hence its creator block is a compression of the creator for
the actual coefficient submatrix B_(A union F,{0,1}), and

    ||block|| <= || |B_(A union F,{0,1})| ||.                (18)

This uses the established deterministic absolute-coefficient domination
of the full multiplication operator, followed by creator compression.
The selected submatrix has at most 2(k+1) original entries. On each
row-return block (17), the full set F is held fixed, and only the n
rungs A can be completed; after removing those spectator flags, the
same argument uses B_(A,{0,1}), with at most 2k entries.

For p>=1, the event aligning all s original signs of a selected
submatrix has probability 2^-s and attains its absolute coefficient
norm against fixed nonnegative singular vectors. Conditional
expectation in the other original signs then gives

    ||C_(ret,k)|| <= 2^(2(k+1)/p) R_B(p).                   (19)

The raw return operator is a direct sum of the two current-side maps,
and their relevant Grams are block diagonal as above, so their maximum,
not their sum, is charged. No optimization over random vectors or
resampling of copied coefficients is used. The fresh-output Gram is
diagonal and at most the original vertex-variance operator V_B. Thus,
for arbitrary real weights on K_(a,2),

    C_k* C_k <= V_B + 2^(4(k+1)/p) R_B(p)^2 I.              (20)

For k>=1, one concrete readout is

    C_k* C_k <= V_B + 4 R_B(4k)^2 I.                       (21)

At grade zero the creator Gram is exactly V_B. The total heavy feedback
count of K_(a,2) can be a-1, far larger than k. This sufficient-family
conclusion is useful because it is derived from retained occupations
and a local original coefficient support, not from folding all fibers
to the full B. Folding first to the full coefficient matrix can charge
all a rungs, including arbitrarily many unoccupied ones. The unrestricted
matrix case still lacks this two-column support localization, and (21)
does not purport to solve it.

For an explicit root-reachable calibration at all relevant orders, take
eta={r0}. At even grade k=4m>=4, choose U of 2m other rows. The output-
column block has A={r0},F=U and the two-by-two Gram

    a a* + diag(sum_(i in U)b_(i,0)^2,
                sum_(i in U)b_(i,1)^2),                    (22)

where a=(b_(r0,0),b_(r0,1)). Its inputs consist of a root-current state
with all rungs U full, and the two one-half-at-current-row predecessors
for every i in U. Each latter predecessor has connected support and
the root-to-current Euler boundary, so has an actual k-step trail.
The root-current input does not contain r0 in its occupied support; its
shortest realization has length k+2, using one root edge twice as a
connector. Thus the whole block is available in the actual root ball
of radius k+2, with its outputs realized in k+1 steps. It is not falsely
inserted into the smaller exact-k reachable compression. For unit
coefficients (22) has norm squared 2m+2, displaying the occupied-rung
dependence while the ambient number of rows is unrestricted.

## 6. What a fold must retain at the next interaction

For equal rungs, the normalized constant profiles on each paired Boolean
level are an exact norm-preserving fold by (14)–(16). Their coefficients
contain the actual layer sizes and predecessor counts. This fold is not
the unweighted identification of all copies of the same current column.
For unequal rungs, a fixed constant profile need not be invariant and
can miss the top norm; (5) gives the exact criterion and residual.

The retained object consists of the original eta, half-rung set A,
fully occupied set F, orientation or Boolean-layer register, the
diagonals (12) or (17), and the signed original rung products in I_r.
Creation and cancellation update these original sets and orientations.
An inserted edge can move a rung from empty to half or from half to
full, transferring a coefficient from an orientation cross into the
full-rung diagonal. Two creators sharing a rung therefore cannot be
treated as independent copies of one two-by-two coefficient fold.

The exact positive Gram identities, including (3)–(5),(11),(17), survive
common congruences on their actual boundary. A common next left map
requires transport of both folded and difference channels. Changing
the original random-variable identification changes the flag algebra
and must be rederived. Actual SparseStack and consumed-SRHT transfers
of the shared original square are developed by the companion branch;
neither a whole-row Gram identity nor a frame claim is inferred from
the scalar bound (19).

The two-row/column family supports an exact rung register with at most
2^|A| orientation states in a fixed block, or binomial-size paired
levels. Constructing and applying the full occupation matrix can still
be exponential. The formulas avoid enumerating sign realizations, but
do not supply an uncharged polynomial-time general moment algorithm.
Computing R_B or selecting useful analogous supports on a general
matrix remains a separate problem.

## 7. Limits relative to the unchanged MI-32 objective

This note distinguishes three different operations: a scalar comparison
with the absolute coefficient norm, a normalized isometric fold of an
actual occupation fiber, and a positive boundary that can be transported
through another interaction. Equation (2) shows why the first cannot
replace the third. Equations (8)–(17) identify exactly what survives in
a family with arbitrarily many original four-cycles. The local support
argument then reaches the weak-moment scale on that same family.

The later count-block localization in Section 9 applies to arbitrary
weighted-sign support. Together with the separately reviewed
[small-row moment and hypercontractive argument](weighted_sign_localization.md),
it now gives the local weighted-sign upper bound and its original
vertex-variance Gram budget. This extends beyond the two-column rung
calibration proved earlier in this note. General regular laws still
require their original multiplicity or vacuum-amplitude data in
addition to parity; the companion conditional-ratio branch does not
automatically identify its counts with these flags. No full-law MI-32
solution, Graph Matrices separator theorem, SRHT sampling endpoint,
quantile conclusion, or novelty claim is made.

## 8. Exact finite evidence

[The verifier](verify_cycle_fiber_geometry.py) checks a signed,
unequally weighted K_(4,2) at grades 0 through 7. It constructs the
actual original-edge return maps and verifies 16 global Gram equalities:
(8)–(10) for column outputs and (17) for row outputs at every grade.
It separately checks 1,056 state-invariant assertions and classifies
all 36 grade-two return components into 24 active square paths, eight
three-stars, and four twelve-cycles. These are raw-state checks with
explicit scope, not a claim of one common reachable root.

The same bounded script checks the Boolean inclusion row/column degrees
through n=7 and 112 exact characteristic identities for (16), plus two
all-positive projected-square equalities and three rational checks of
the non-preserving uniform fold. No floating-point spectrum or R_B
supremum is evaluated. The universal identities, norm arguments,
local-support reduction, and root-distance statement are analytic.
The report pins this note and its standalone verifier by SHA-256.

## 9. Exact occupation-count localization for arbitrary bipartite support

The local-support step has an exact generalization that does not require
two columns. This section proves the geometry only; any subsequent
hypercontractive or strong/weak moment argument needs its own complete
proof and is not assumed here.

For an arbitrary finite simple bipartite B, restrict the full creator's
outputs to current column vertices. For every occupied set T define its
entire row-count vector

    d_i(T)=#{e in T: e belongs to original row i}.

Then C_k C_k* on these column-current outputs is block diagonal in d.
Indeed two outputs with a common predecessor have the form

    (j,S union {ij}),       (j',S union {ij'}),

with the same current predecessor row i. Replacing the added edge
changes its column but preserves the count at every row. The diagonal
case is included. Cancellations among signed contributions cannot
create entries outside these structural blocks.

In a nonzero block, put I={i:d_i>0}. Since sum_i d_i=k+1,
|I|<=k+1. Every predecessor of a block output (j,T) is

    (i,T minus {ij}),       ij in T,

so its current row belongs to I and all its flags belong to the
original submatrix B_I on rows I and all original columns. Embed these
states into the raw domain of C_k(B_I), using the actual bijection of
its local edges with the same original edges. Select the same output
states with count vector d. This reproduces the block factor exactly:

    block_d = P_d C_k(B_I) E_d,                             (23)

where E_d includes precisely the predecessor basis states, and P_d is
the indicated output projection. Any other domain basis state of
C_k(B_I) is zero on those selected output rows. Thus one may omit E_d
for the purpose of the norm upper bound, obtaining

    ||block_d|| <= ||C_k(B_I)||.                            (24)

This is a legitimate enlargement of available outputs or predecessors,
not an identification of random variables. Original signs are neither
copied nor resampled. Zero output rows and unavailable basis states
cause no issue; the latter are further genuine compressions.

The transposed argument shows that row-current outputs preserve the
entire column-count vector and use at most k+1 original columns J.
The two current-side maps have orthogonal domains and ranges. Hence
the full raw creator satisfies the exact geometric norm reduction

    ||C_k(B)|| <= max{
        max_(I: |I|<=k+1) ||C_k(B_I)||,
        max_(J: |J|<=k+1) ||C_k(B^J)|| }.                   (25)

Sets larger than the actual row or column dimension are unnecessary.
The empty zero map is harmless. The reverse inequality also holds
because each submatrix creator embeds by zeroing all flags outside its
original support and projecting vertices, so (25) may be written as
equality. The upper direction is the one needed for subsequent work.

An arbitrary non-diagonal identification of input basis states can
change the output Gram and its block structure; (23) is not asserted
after such an operation without rederivation. Actual basis masks do
preserve this structural zero pattern. This localization alone is not
a weak-moment bound. In particular, replacing each submatrix creator
by an unproved sharp random-matrix estimate would simply move the
missing analytic step rather than resolve it.

Additional bounded exact checks in the same verifier use a signed,
unequally weighted three-by-four support with nine nonzero entries at
grades zero through four. They check the shared-predecessor count
invariant, the size of the selected original axis, and independently
rebuild each factor using locally enumerated flags embedded by its
original edge IDs. Its report distinguishes these checks from the
preceding two-column identities and makes no claim to test a moment
or hypercontractive endpoint.

## 10. A supplied Parseval row insertion and the retained count budget

The matrix-unit geometry need not remain an exact decomposition after
another coefficient interface. Here is a concrete continuation on the
same K_(a,2), together with the positive budget that remains valid.

Let C denote the row-to-column creator and let R:E->R^a be a supplied
coefficient insertion into its current-row register, independent of
the original occupation flags. Apply this insertion first and then
consume the row with the actual creator:

    C_R = C(R tensor I_flags),
    C_R C_R* = C(RR* tensor I_flags)C*.                     (26)

Cross terms between creators at original rows i and i' now have
coefficient (RR*)_(i,i'). If i differs from i', they can transfer one
unit of occupation count between those rows. Thus a Parseval condition
R*R=I_E does not imply exact row-count block diagonality: RR* is a
projection and need not be diagonal in the original row basis.

Take E=R, all original b_(i,t)=1, grade zero, and

    R(1)=(1,...,1)/sqrt(a).

This is the analysis map of the supplied one-dimensional Parseval frame
u_i=1/sqrt(a). The original vacuum creator has input basis |i,empty>
and output basis |ct,{(i,ct)}>, with i=1,...,a and t=0,1. These 2a
outputs are distinct original flag states even when their current
column vertex is the same. Write v_i for the output vector that is
one on the two outputs of row i and zero elsewhere. Then

    CC* = sum_i v_i v_i*,
    C_R C_R* = (1/a)(sum_i v_i)(sum_i v_i)* = (1/a)J_(2a).  (27)

The latter Gram has norm two. Its row-count pinching deletes all
cross-row blocks, leaving a blocks (1/a)J_2 and norm 2/a. The squared
norm allowance therefore loses a factor a if exact count decomposition
is incorrectly assumed after the insertion. Every input and output
here is an actual vacuum or one-step original state; the coherence is
supplied by the normalized coefficient map R, not by a changed sign law.

The correct positive comparison is nevertheless inexpensive. Whenever
a **derived** row-diagonal majorant is available,

    RR* <= diag(g_i),       g_i>=0,

one has the genuine unpinched output budget

    C_R C_R* <= C(diag(g_i) tensor I_flags)C*.               (28)

The right side preserves row-count blocks: it is the output Gram of
the creator with original row coefficients scaled by sqrt(g_i). This
is not pinching the left side. For a Parseval analysis R, RR*<=I, so
g_i=1 is always available. In the example (27) its exact positive loss
is

    CC* - C_R C_R*
      = (1/a)sum_(i<j)(v_i-v_j)(v_i-v_j)*.                  (29)

For a general bounded R, g_i=||R||^2 is a valid scalar choice; a sharper
supplied diagonal majorant may retain more coefficient information.
Any common next output map L transports (26),(28),(29) by congruence,
including both coherent and difference channels. An insertion that
depends on occupation, changes original variables, or has noncommuting
auxiliary blocks needs its actual RR* on that interface; it is not
licensed by this scalar row-map example.

This is an explicitly supplied Parseval insertion followed by actual
matrix-unit row consumption. It is not asserted to be the unmodified
primitive SparseStack or consumed-SRHT operator. Matching those models
requires their own ordered coefficient and child Grams, as developed
in the companion [cycle transfer](cycle_transfer.md). In particular no
SRHT endpoint follows from ignoring the count cross terms in (26).

Sixteen additional exact assertions at a=2,3,4,5 reconstruct (27) from
the original vacuum matrix units and the rational Gram RR*=J_a/a,
verify the two exact row-sum eigenvalues, and verify the complete
positive difference-square identity (29). The irrational entries of R
are used only through this exact rational Gram; no numerical spectral
approximation or unrelated test expansion is involved.
