# A repeated four-cycle as an original-edge moment contraction

Date: 2026-09-13. Status: analytic identities, an explicit positive excursion contraction, and a counterexample to resetting its shared-edge budget. This continues the full-law branch of [vacuum_multiplicity_budget.md](../mi32_profile_2026-09-13/vacuum_multiplicity_budget.md). It does not prove the full MI-32 estimate, either amplitude-transfer statement, or a comparison of quantiles.

The common test family is the weighted support K_(a,2), with original row labels i and two original column labels 0,1. Its transpose is K_(2,a). The four-cycle computation also works on K_(a,b) and on arbitrary subgraphs, with zero coefficients omitted. The relevant objects here are even moments and original-edge half-multiplicities. They are not the parity flags or local Jacobi degrees of another representation.

## 1. The exact conditional budget is an even tilt

Let Y_e be independent symmetric real entries, with every absolute moment finite. Omit entries that vanish almost surely. Put

    m_(e,p)=E|Y_e|^p,        m_(e,0)=1,
    w(r)=product_e m_(e,2r_e),
    v_e(r)=m_(e,2r_e+2)/m_(e,2r_e),                      (1)

for a nonnegative integer multiindex r on the original edges. The total pair count is |r|=sum_e r_e. Define the product probability law

    dP_r(Y)=[product_e |Y_e|^(2r_e)/w(r)] dP(Y).          (2)

It is a genuine probability law, and the original entries remain independent and symmetric under it. It is a moment-weighted law, not conditioning on observed entries or introducing replacement variables. In particular,

    E_r Y_e^2=v_e(r),
    E[P(Y) product_e Y_e^(2r_e)]=w(r) E_r P(Y)           (3)

for every integrable polynomial P. Fresh edges have v_e(r)=E Y_e^2. An occupied edge uses its actual next moment ratio. More generally, for any nonnegative integer increment d,

    Delta_d(r)=w(r+d)/w(r)
       =product_e product_(h=0 to d_e-1)
            m_(e,2r_e+2h+2)/m_(e,2r_e+2h).              (4)

There is an exact overlap identity

    Delta_d(r) Delta_f(r+d)
         =Delta_f(r) Delta_d(r+f)=w(r+d+f)/w(r).         (5)

Thus successive cuts or insertions retain a consistent budget even when they share original edges. Keeping r, rather than resetting an edge to its original variance, is essential. No uniform cutoff norm or single horizon height is used.

For alpha-regular original entries, meaning ||Y_e||_(2p)<=alpha||Y_e||_p for p>=1, the previous log-convexity calculation gives

    v_e(r)<=alpha^4 ||Y_e||_(2r_e+2)^2.                 (6)

Use the exact variance in (1) when r_e=0. In particular, the row mass of these current second moments is exactly

    R_i(r)=sum_j E Y_ij^2
              +sum_(j:r_ij>0)[v_ij(r)-E Y_ij^2].       (7)

Every bracket is nonnegative by moment log-convexity. Formula (7) charges high moments only to the occupied original entries. Uniform regularity of the tilted law itself is neither assumed nor needed.

## 2. The first even four-cycle has coefficient 20, or 10 at a fixed root

Fix distinct rows i,k and distinct columns j,l. Consider the closed alternating words of length eight whose four original edges are exactly

    C={(i,j),(i,l),(k,j),(k,l)},

each traversed twice. In the trace of (YY*)^4 there are exactly 20 such words. Ten start at i and ten at k. Each word has the same monomial

    product_(e in C) Y_e^2.                             (8)

This count has a short algebraic derivation. For the 2-by-2 submatrix write its row Gram as [[A,C_0],[C_0,B]]. Then

    tr([[A,C_0],[C_0,B]]^4)
       =A^4+B^4+4(A^2+AB+B^2)C_0^2+2C_0^4.

The coefficient of the product of the four squared entries is 8 from 4AB C_0^2 and 12 from 2C_0^4. The two diagonal entries of the fourth power contribute equally by exchanging the row labels. This proves the rooted count ten without enumerating a sign law.

Consequently, if Q_i is the positive sum of these rooted length-eight words over all rectangles containing row root i, then

    Q_i(Y)=10 sum_(k!=i) sum_(j<l)
                       Y_ij^2 Y_il^2 Y_kj^2 Y_kl^2.    (9)

At the first occurrence r=0 its expected cost uses only the four original variances. Higher entry moments first enter when an extension reuses an edge.

## 3. A variance-matrix contraction of that actual excursion

Under the even tilt r, form the nonnegative rectangular matrix

    V(r)=(v_ij(r)),                                     (10)

with zero at missing support edges. Let R(r) and C(r) be its maximum row and column sums. Its entries are second moments under (2), not standard deviations. Equations (3) and (9) give the exact rooted cost

    Gamma_i(r)=E_r Q_i(Y)
      =10 sum_(k!=i) sum_(j<l)
                       v_ij(r)v_il(r)v_kj(r)v_kl(r).    (11)

Writing V=V(r), this is equivalently

    Gamma_i(r)
      =5 sum_(k!=i){[(VV*)_ik]^2-sum_j V_ij^2 V_kj^2}.

All terms inside braces are nonnegative. Therefore

    Gamma_i(r)
      <=5 [(VV*)^2]_ii
      <=5 ||V||^2 sum_j V_ij^2
      <=5 R(r) C(r) sum_j v_ij(r)^2.                    (12)

The middle inequality is the positive-matrix relation (VV*)^2<=||V||^2 VV*. The last uses ||V||^2<=||V||_1||V||_infinity. Column roots obey the transposed formula. Summing over row roots gives

    E_r sum_i Q_i(Y)
       =20 sum_(i<k,j<l) v_ij v_il v_kj v_kl
       <=5 R(r) C(r) ||V(r)||_F^2.                      (13)

These are actual positive contractions, with an explicit retained profile. They remove the sum over four-cycle locations in favor of current row/column second-moment masses and a row quadratic mass, without replacing each original law by a height H_q. The sharper expression (11) should be retained when its exclusions matter; it is identically zero on a row star or any graph with no four-cycle.

For the common support K_(a,2), put

    c_i(r)=v_(i,0)(r)v_(i,1)(r).

Then the exact formulas simplify to

    Gamma_i(r)=10 c_i(r) sum_(k!=i)c_k(r),
    E_r sum_i Q_i(Y)=20 sum_(i<k)c_i(r)c_k(r).            (14)

The two factors in c_i retain two different original entries and their two different multiplicity counts. This is the squared-amplitude counterpart of the original two-edge rung product in the weighted-sign cycle calculation. An occupied full or half rung in a parity state does not determine these two counts, so no automatic transfer to a parity-only creator bound is asserted.

For a fresh unit-variance K_(a,b), (11) is

    Gamma_i(0)=5(a-1)b(b-1),

while the last bound in (12) is 5ab^2. For K_(a,2) the exact value is 10(a-1). Thus the first four-cycle contraction has no artificial horizon factor. Its multiplicity dependence enters exactly through later updates of (1).

## 4. What can be cut, and how the budget extends

Suppose a closed alternating even word has a specified contiguous eight-step excursion of the type in Section 2, returning to its starting vertex. Erasing those eight steps leaves a closed word and reduces each of the four original-edge multiplicities by two. In particular, the remaining multiplicities are still even. If their half-counts are r, the weight before erasure is exactly

    w(r) product_(e in C) v_e(r).                        (15)

Summing over the ten rooted words and over their possible partner labels is exactly w(r)Gamma_i(r). Inequality (12) supplies the stated conditional contraction. The same calculation applies to any positive even polynomial background

    P(Y)=sum_r a_r product_e Y_e^(2r_e),       a_r>=0:

    E[P(Y)Q_i(Y)]=sum_r a_r w(r)Gamma_i(r).              (16)

This is a positive moment-functional statement; it is not a Loewner inequality on an orthogonal space of multiplicity states.

After the excursion is inserted, update r to r+1_C. A subsequent excursion uses Gamma at that updated multiindex. A two-step excursion on original edge e similarly has exact cost v_e(r) and updates r to r+1_e. Equation (5) proves consistency for arbitrary overlaps, including a repeated square and distinct squares sharing a rung. If the currently retained word has both an occupation state and even-multiplicity data, both must be transported by its actual operations.

The prescribed cut is important. A general even closed word need not admit this contiguous excursion decomposition; its four-cycle occurrences may be interleaved. This note does not silently remove separated occurrences, identify original entries, or prove that every trace word is covered with bounded multiplicity. A future decomposition must give its actual cut sites and charge any resulting multiplicity of representation. Equations (11)-(16) remain valid building blocks for such a decomposition, rather than an asserted estimate of the entire trace by one excursion.

For all concatenations at one fixed row root in K_(a,2), there is also an exact contraction over the other rungs. Define

    Z_i=Y_(i,0)^2Y_(i,1)^2.

Then Q_i=10 Z_i sum_(k!=i)Z_k, and the Z_k are independent. Hence for every integer ell>=1,

    E Q_i^ell
       =10^ell m_(i,0,2ell)m_(i,1,2ell)
                         E[(sum_(k!=i)Z_k)^ell].        (17)

This sums all such concatenated four-cycle excursions, including repeated partner labels. The moment ratio for an occupied rung factor Z_k is exactly

    E Z_k^(h+1)/E Z_k^h
       =v_(k,0)(h)v_(k,1)(h),                           (18)

where v_(k,t)(h)=m_(k,t,2h+2)/m_(k,t,2h). Both edges are raised here because this particular excursion family traverses them together. Backgrounds with unequal counts still use (14), not (18) with an invented common count.

## 5. Gaussian calibration and explicit allocation costs

For independent centered Gaussian entries with variances beta_e,

    v_e(r)=(2r_e+1)beta_e.                              (19)

In particular, for a fixed row i,

    R_i(r)=sum_j beta_ij+2sum_j r_ij beta_ij.             (20)

Fresh variance is unchanged. If t=|r| and beta_*=max_e beta_e, write R_0,C_0 for the original maximum row/column variance sums and S_i,0=sum_j beta_ij^2. Then

    R(r)<=R_0+2t beta_*,       C(r)<=C_0+2t beta_*,
    sum_j v_ij(r)^2
       <=S_i,0+4 beta_*^2(t_i+t_i^2),
    t_i=sum_j r_ij<=t.                                  (21)

Together with (12), this gives an explicit four-pair insertion bound. At total background count t its worst scalar cost grows at most as a constant times t^4 beta_*^4, with the original variance masses and the actual row count t_i retained in the displayed formula. A four-pair insertion on one heavily used Gaussian square can indeed have order t^4. There is no charge of a horizon-t tail size to every untouched entry.

The row-star calibration can be checked exactly, including its extensions. Let S=sum_(e incident to root)Y_e^2 for a Gaussian row star and let sigma^2=sum_e beta_e. Expand S^q into its original even monomials. At a monomial of total count q, its next two-step insertion has cost sum_e(2r_e+1)beta_e<=sigma^2+2q beta_*. Consequently

    E S^q<=product_(h=0 to q-1)(sigma^2+2h beta_*),
    ||sqrt(S)||_(2q)<=sqrt(sigma^2+2(q-1)beta_*).         (22)

For d unit-variance Gaussian edges there is equality in the first formula:

    E S^q=product_(h=0 to q-1)(d+2h).                    (23)

For m disjoint such stars, a union-moment estimate gives

    E max_(i<=m) sqrt(S_i)
          <=m^(1/(2q))sqrt(d+2(q-1)).                   (24)

At q comparable to ln m this has the correct sqrt(d)+sqrt(q) scale, including d of order q/ln q. Thus the conditional budget passes the Gaussian-star calibration that the previous static three-point envelope failed. This calibration is not offered as a new endpoint theorem for stars.

For the concatenated K_(a,2) family (17) with unit Gaussians, the positive rung variable Z has moment ratio (2h+1)^2. Put d=a-1 and B=sum_(k!=i)Z_k. At a monomial of B^h with counts h_k summing to h, its next summed rung insertion costs

    sum_k(2h_k+1)^2=d+4h+4sum_k h_k^2<=d+4h(h+1).

Thus a second explicit contraction is

    E B^ell<=product_(h=0 to ell-1)[d+4h(h+1)],
    E Q_i^ell<=10^ell[(2ell-1)!!]^2
                        product_(h=0 to ell-1)[d+4h(h+1)]. (25)

The total length here is 8ell. The quadratic repeated-rung cost in (25) records the original two-edge reuse. It is not replaced by independent fresh rung products. Formula (25) bounds this genuine family of interacting repeated squares but does not cover arbitrary row-switching/interleaved trace words.

For general alpha-regular entries, the main budget remains (1),(11), and (14), with actual local orders at most the total horizon. One coarse polynomial readout follows by iterating regularity in (6): for r_e>=1,

    v_e(r)/E Y_e^2
       <=alpha^(4+2ceil(log_2(r_e+1))).                  (26)

This can be large and is not proposed as a sharp MI-32 closure. The information preserved by (1) is more useful than replacing every r_e by the horizon before the contraction. No constant-factor control of the resulting full regular-law profile by the original weak moment is established here.

## 6. A precise false cycle-cutting budget

Consider the proposed rule: integrate every even square excursion at its fresh product of four original variances, then compose these scalar costs even when later squares reuse a rung. The rule is false already for unit Gaussian entries on K_(3,2).

Take root row 0, first square using partner row 1, and second square using distinct partner row 2. Before the first excursion every next-edge cost is one. After it, the two root-rung edges have count one. The second excursion therefore costs

    3*3*1*1=9                                          (27)

instead of its fresh cost one. Equivalently, the product monomial has fourth moments on the two root edges and second moments on its four other edges, so its expectation is 9. Including all ten words for each prescribed square makes the two values 900 and the proposed 100. All variables are the original independent entries; the failure comes from genuine shared-edge use, not dependence inserted into the law.

Repeating the same square twice gives an even stronger smallest example on K_(2,2): all four edges have fourth moments, producing 3^4=81 rather than one, or 8100 rather than 100 after the ten-word factors. Adding just a two-step backtrack on one edge after its first square already produces a length-ten word with an extra cost 3 rather than one.

At ell repetitions of the same square, the exact scalar monomial cost is

    [(2ell-1)!!]^4.                                    (28)

It cannot be bounded by C^ell times the fresh cost for one absolute C: its ell-th root grows on the order of ell^4. A horizon-dependent loss large enough to hide this must be charged explicitly. The updated ratios in (4) give the exact dependence instead.

These examples refute only that specified scalar reset rule, including the variant that regards different square labels as independent despite a shared rung. They do not refute a cycle contraction carrying the counts r_e, the occupied-output Gram, or a correctly charged horizon-dependent allowance. They are not counterexamples to MI-32.

## 7. Cost, established methods, and remaining work

Given the required scalar moments, the profile (1) costs one ratio for each retained occupied original edge; fresh edges use their original variances. On K_(a,2), (14) can be evaluated in O(a) arithmetic after those ratios are supplied. Computing all general rectangular costs (11) can use VV* or direct rectangle sums; (12) instead needs row/column sums and row quadratic masses, in O(number of support edges) arithmetic. These statements do not make moment acquisition, bit growth, or a large family of distinct multiindices free.

The pair counts up to horizon q have up to binom(N+q,q) possible multiindices for N original edges. A global walk contraction would need to avoid enumerating them while retaining enough of their allocation and the actual parity/current-vertex interface. Original-variable identification changes both the product law and this state data and requires a new derivation. Adding an independent original entry introduces its own moments and count. Adding or reusing an edge on the same original support updates (1), not a new independent flag.

Positive original-entry trace expansion and moment comparison are established techniques; see [Bandeira–van Handel, the rectangular trace expansion and Corollary 3.2](https://arxiv.org/pdf/1408.6185). The Gaussian recursion (19) is the elementary Gaussian integration-by-parts moment recursion; (22)-(23) recover standard chi-square moment behavior. No novelty claim is made for even tilting, Cauchy-Schwarz, or these scalar formulas. The continuation here is their explicit rooted four-cycle contraction with the original-edge update and its demonstrated shared-rung obstruction.

The task left by this result is concrete: combine the actual parity/current-vertex cycle interface with the local multiplicity data, or provide a justified word decomposition with charged cut multiplicity. Contiguous closed excursions can be contracted as above. Interleaved cycle words are not covered automatically. The full regular-law weak-moment comparison and full MI-32 objective remain open.

## 8. Bounded exact verification

The [verifier](verify_cycle_multiplicity.py) and [report](cycle_multiplicity_checks.json) record 693 passing exact checks. They enumerate the actual length-eight alternating words on K_(2,2), K_(3,2), and K_(3,3), retaining the chronological word, its row root, and its original four edges. Eighteen selected law/background cases compare that word sum with (11), the Gram subtraction identity, the rung formula when applicable, and rational positive certificates for the row/column bound. The entry moment tables come from scaled symmetric four-point laws and scaled Gaussians.

Separate checks verify overlapping increment identities, the exact factors 3,9,81 against the specified reset rule, Gaussian row-star moments through q=8 by independent multinomial convolution, and the repeated-rung allocation bound through seven concatenated square excursions. All arithmetic is rational; there is no numerical eigensolver. These checks support the proofs, not arbitrary interleaved-word coverage, an efficient full moment algorithm, or the open endpoint. The report pins this note and its verifier.
