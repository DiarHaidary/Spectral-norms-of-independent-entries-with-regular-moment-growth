# The same rung lowering and four-edge cycle at the original Parseval and consumed interfaces

Date: 2026-09-13. Status: proved derivation; an independent full analytic review passed with no mathematical correction. Bounded checks and their scope are recorded at the end. This note transfers the actual \(K_{m,2}\) half-rung mechanism, rather than merely comparing scalar bounds between models. It uses the same original four-edge cycle for its two-creation and row-equality calculation. The general ordered-cycle positive rule is in [ordered_cycle_boundary.md](ordered_cycle_boundary.md). Earlier checkpoints remain unchanged.

## 1. Original edge labels give an actual collective Parseval cross

Let the original graph have rows \(i\in[m]\), columns \(0,1\), and edge labels \(j_i=(i,0)\), \(o_i=(i,1)\). Write its real coefficients as \(a_i,b_i\), respectively. For this transfer supply the explicit normalization
\[
 a_i^2+b_i^2=1\quad(i\in[m]),\qquad
 u_{j_i}=a_i e_i,\quad u_{o_i}=b_i e_i.
 \tag{1.1}
\]
Thus these \(n=2m\) original edge-indexed vectors form a Parseval frame in \(\mathbb R^m\). This is a supplied row-normalized graph class, not a claim that arbitrary graph weights can be normalized without changing the problem. Every original edge keeps its own flag. In particular the two edges of a rung are never replaced by one random variable.

Take the exceptional set \(J=\{j_i\}\) and the ordinary set \(O=\{o_i\}\). There can be arbitrarily many exceptional coefficient directions. To exhibit the original current-column interface as well as the projection residual, use auxiliary space \(H=\mathbb C^2_{\rm current}\otimes\mathbb C^2_{\rm orbit}\), flip \(X\), and
\[
 Q=I\otimes\operatorname{diag}(1,0),\quad \Delta=I-2Q,
 \quad N_{j_i}=I\otimes X,\quad N_{o_i}=X\otimes I.
 \tag{1.2}
\]
The ordinary marks preserve \(Q\); every exceptional mark sends it to \(I-Q\). They are supplied commuting unitaries. Put
\[
 C=\sum_eu_e\otimes N_e^*\otimes c_e,
 \quad F=QC-CQ=\sum_i u_{j_i}\otimes N_{j_i}^*\Delta\otimes c_{j_i},
 \quad C_O=\sum_i u_{o_i}\otimes N_{o_i}^*\otimes c_{o_i}.
 \tag{1.3}
\]
These are the primitive SparseStack row-interface creators on their original hard-core flags. The marks are an explicit marked continuation of that interface, not asserted to occur in the unmodified distribution.

For a direct graph-interface check, prepare the orbit factor in \(|+\rangle\) and project the output current factor onto \(|0\rangle\). The original current input \(|t\rangle\) then permits precisely edge \((i,t)\); the output coefficient is the new row vertex \(i\). Thus this specified compression of \(C\) is exactly the column-to-row graph creator, with its original occupation set retained. It explains the shared family at the operator level; no identification of edge signs is used.

Because coefficients from different rungs are orthogonal, ordered multiplication gives the exact cross
\[
 \boxed{\quad K=F^*C_O
     =V\otimes\sum_i\kappa_i c_{j_i}^*c_{o_i},
 \qquad \kappa_i=a_i b_i,
 \quad V=(X\otimes I)(I\otimes\Delta_{\rm orbit}X),\quad V^*V=I.\quad}
 \tag{1.4}
\]
The order in the orbit factor is \(\Delta_{\rm orbit}X\), not \(X\Delta_{\rm orbit}\). The scalar coefficients \(\kappa_i\) are exactly the original rung products in the graph output Gram.

Fix the full rungs \(F_0\), the empty rungs, and the active half-rungs \(I_0\), with \(|I_0|=M\). A half-rung contains exactly one of its two original flags. Let \(q\) be the number of active exceptional flags. The total input grade is \(r=M+2|F_0|\), and the total exceptional count is \(q+|F_0|\). Full and empty rungs are annihilated by each summand of (1.4); these sectors are genuine spectators. On the half-rungs,
\[
 K=V\otimes D_q(\kappa),\qquad
 D_q(\kappa)=\sum_{i\in I_0}\kappa_i\sigma_i^-,
 \quad D_q:\ell^2\binom{I_0}{q}\longrightarrow\ell^2\binom{I_0}{q-1}.
 \tag{1.5}
\]
This is the weighted adjacent-layer Boolean lowering that occurs in the original \(K_{m,2}\) cycle fibers. The full-rung diagonal energies in the graph output Gram are additional data; (1.5) transfers its off-diagonal rung mechanism, not the entire graph theorem by analogy.

For \(1\le q\le M\), direct weighted insertion gives
\[
 \|D_q(\kappa)\|^2\le
     \min\{q,M-q+1\}\sum_{i\in I_0}|\kappa_i|^2.
 \tag{1.6}
\]
If all \(|\kappa_i|=\kappa\), an occupation phase gauge removes their signs and
\[
 \boxed{\quad\|D_q(\kappa)\|^2=\kappa^2 q(M-q+1).\quad}
 \tag{1.7}
\]
Indeed the unweighted inclusion matrix has column sum \(q\), row sum \(M-q+1\), and the two uniform layer vectors attain the resulting norm. This collective scale cannot be obtained by treating the overlapping four-cycle exchanges as independent disjoint channels.

## 2. The actual consumed cross retains ordered child products

Supply \(A,B\in U(n)\), flat \(B\), and a row set \(T\). On child grade \(s\), retain the original operators
\[
 L_{e,T}=\sum_a\overline{B_{ae}}c_{y,a}\langle a|A^*I_T,
 \quad
 \mathcal C_T=\sum_e u_e\otimes N_e^*\otimes c_{x,e}\otimes L_{e,T},
 \quad \mathcal E_T=Q\mathcal C_T-\mathcal C_TQ.
 \tag{2.1}
\]
They consume the actual row register. The original \(x_e\) and \(y_a\) flag algebras remain unchanged. For the same fixed half-rung sector, define
\[
 Z_i=L_{j_i,T}^*L_{o_i,T}:
       \ell^2(T)\otimes Y_s\longrightarrow\ell^2(T)\otimes Y_s.
\]
Then the actual model cross is exactly
\[
 \boxed{\quad\mathcal K_T=\mathcal E_T^*\mathcal C_{O,T}
       =V\otimes\sum_{i\in I_0}\kappa_i\sigma_i^-\otimes Z_i.\quad}
 \tag{2.2}
\]
In particular its input Gram contains
\[
 \mathcal K_T^*\mathcal K_T
   =\sum_i\kappa_i^2 n_i\otimes Z_i^*Z_i
      +\sum_{i\ne l}\kappa_i\kappa_l
                         \sigma_i^+\sigma_l^-\otimes Z_i^*Z_l.
 \tag{2.3}
\]
The auxiliary identity is suppressed. The ordered products \(Z_i^*Z_l\) are the actual shared output Gram read by an interaction. In general they are neither scalars nor interchangeable with \(Z_l^*Z_i\).

There is an exact collective positive difference. At an output half-rung subset \(S\) of size \(q-1\), put
\(z_i=\kappa_iZ_i f(S\cup\{i\})\), \(i\notin S\). Then
\[
 (M-q+1)\sum_{i\notin S}\|z_i\|^2
          -\left\|\sum_{i\notin S}z_i\right\|^2
       =\sum_{\{i,l\}\subset I_0\setminus S}\|z_i-z_l\|^2.
 \tag{2.4}
\]
Thus the positive bound retains the child operators on the input:
\[
 \mathcal K_T^*\mathcal K_T\preceq
        (M-q+1)\sum_i\kappa_i^2 n_i\otimes Z_i^*Z_i.
 \tag{2.5}
\]
A second weighted output Cauchy bound, using \(\|Z_i\|\le z_i^{\max}\), gives \(q\sum_i\kappa_i^2(z_i^{\max})^2\). Since flatness and row compression give \(\|Z_i\|\le(s+1)/n\),
\[
 \|\mathcal K_T\|^2\le
  \frac{(s+1)^2}{n^2}\min\{q,M-q+1\}\sum_i\kappa_i^2.
 \tag{2.6}
\]
The actual Gram (2.3) and the squares (2.4) are retained before this scalar readout. No independent child flag is introduced for a rung or a pair.

At child vacuum there is a stronger exact collective transfer. With all rows,
\[
 Z_i=A\operatorname{diag}_a(B_{a,j_i}\overline{B_{a,o_i}})A^*
       =\frac1n A\operatorname{diag}_a(\zeta_i(a))A^*,
 \qquad |\zeta_i(a)|=1.
 \tag{2.7}
\]
In each row mode \(a\), the phases \(\zeta_i(a)\) are removed by a diagonal unitary on the original half-rung occupations. Consequently the full cross is unitarily equivalent to copies of \(D_q(\kappa)/n\), with its auxiliary unitary retained. In particular
\[
 \boxed{\quad
 \|\mathcal K_{[n]}|_{s=0}\|^2=\frac{\|D_q(\kappa)\|^2}{n^2},
 \qquad
 \|\mathcal K_T|_{s=0}\|^2\le\frac{\|D_q(\kappa)\|^2}{n^2}.\quad}
 \tag{2.8}
\]
The second statement follows because \(\mathcal K_T\) is the actual common row compression of the full-row cross. In the equal-weight case this gives \(\kappa^2 q(M-q+1)/n^2\), without a further factor for the number of interacting cycles. This exact equivalence is asserted at child vacuum; (2.3) is the retained interface at positive child grade.

## 3. The four original labels expose the nilpotent cycle inside that Gram

Take two active rungs, indexed 0 and 1. The two matching occupations are
\[
 B_0=\{j_0,o_1\},\qquad B_1=\{o_0,j_1\}.
\]
The first lowering channel sends \(B_0\) to \(\{o_0,o_1\}\); the second sends \(B_1\) there. Their ordered product is the original four-edge cycle word
\[
 W=(c_{j_1}^*c_{o_1})^*(c_{j_0}^*c_{o_0}),
 \qquad W|B_0\rangle=|B_1\rangle,
 \quad W^2=0,
 \quad W^*W=P_0,\quad WW^*=P_1,
 \tag{3.1}
\]
where \(P_0,P_1\) retain the two actual matching masks and any spectator occupations. This is the graph transition path around the same square, not four copied transition signs. Its primitive coefficient is \(\kappa_0\kappa_1\). The actual consumed cycle contribution in (2.3) is
\[
 \Omega=\kappa_0\kappa_1\{
      W\otimes Z_1^*Z_0+W^*\otimes Z_0^*Z_1\}.
 \tag{3.2}
\]
The ordered-cycle rule applies because these initial and final masks are orthogonal. In particular
\[
 \|\Omega\|=|\kappa_0\kappa_1|\,\|Z_1^*Z_0\|,
 \quad
 \Omega\preceq|\kappa_0\kappa_1|
     \{P_0\otimes|Z_1^*Z_0|+P_1\otimes|(Z_1^*Z_0)^*|\}.
 \tag{3.3}
\]
This keeps the actual child Gram and both occupation masks; the triangle estimate on the two summands has an unnecessary factor two. Equations (2.3)--(2.8), however, still assemble the different overlapping squares collectively. One must not infer a global disjointness assertion from the two masks of one square.

At full rows and child vacuum, each \(Z_i\) is \(1/n\) times a unitary, so (3.3) has exact norm \(|\kappa_0\kappa_1|/n^2\). A subsequent operation on row/child registers changes the ordered child factor while retaining the original \(x\)-matching masks. A proposed operation that instead identifies original edge variables changes (3.1) and requires a new parity calculation.

## 4. One actual additional creation and row equality on the same square

Here the interaction is the original two-round projection residual
\[
 \mathcal R^{(2)}=Q\mathcal C_{T_2,\mathrm{next}}\mathcal C_{T_1}
                   -\mathcal C_{T_2,\mathrm{next}}\mathcal C_{T_1}Q.
 \tag{4.1}
\]
It consumes both original row registers, retaining the ordered coefficient output. Take \(m=2\), label \((j_0,o_0,j_1,o_1)=(0,1,2,3)\), restrict its input flags to \(B_0,B_1\), and project the ordered output coefficient onto \(e_1\otimes e_0\) and its output \(x\)-support onto all four edges. These actual input/output projections select exactly two paths:

* From \(B_0\), create \(o_0\) first, then \(j_1\).
* From \(B_1\), create \(j_0\) first, then \(o_1\).

There are no omitted paths with that ordered coefficient output. Each path has one exceptional and one ordinary creation. Their auxiliary residual is the same unitary
\(U=(N_{j_1}N_{o_0})^*\Delta=(N_{o_1}N_{j_0})^*\Delta\).
Define the actual two-row child maps
\[
 F_{ba}=L_{b,T_2}^{(s+1)}(I_{T_2}\otimes L_{a,T_1}^{(s)}),
 \qquad d_0=b_0a_1,\quad d_1=a_0b_1.
 \tag{4.2}
\]
Up to the common unitary and the displayed one-dimensional coefficient/output flag factors, the compressed residual is exactly
\[
 \boxed{\quad R=[d_0F_{2,1},\ d_1F_{3,0}],\qquad
 R^*R=\begin{pmatrix}
 d_0^2F_{2,1}^*F_{2,1}&d_0d_1F_{2,1}^*F_{3,0}\\
 d_0d_1F_{3,0}^*F_{2,1}&d_1^2F_{3,0}^*F_{3,0}
 \end{pmatrix}.\quad}
 \tag{4.3}
\]
Here \(d_0d_1=\kappa_0\kappa_1\), the same four original edge product as (3.2). The off-diagonal label map is again the matching exchange \(W\) or its adjoint. The next creation has replaced its child factor by the actual ordered pair Gram, not removed its occupation memory.

Now set \(T_1=T_2=T\) and apply the actual row equality \(I_{\rm eq}|j\rangle=|j,j\rangle\). Writing \(h_{j,i}=\sum_a\overline{A_{ja}B_{ai}}c_{y,a}\),
\[
 F_{ba}I_{\rm eq}=\mathcal H_{ba}
              :=\sum_{j\in T}h_{j,b}h_{j,a}\langle j|.
 \tag{4.4}
\]
Hard-core commutation gives \(\mathcal H_{ba}=\mathcal H_{ab}\) for the *same unordered original pair*. It does not identify the distinct pairs \(\{2,1\}\) and \(\{3,0\}\). This distinction is exactly what the interacting square can read.

For a concrete exact calculation, use all four rows, child vacuum, and \(A=B=H_4/2\), the real normalized Walsh transform, with binary indices \(0,1,2,3\). For a two-child support \(\{a,b\}\), the two terms in (4.4) cancel unless
\((a\mathbin{\mathrm{xor}}b)\cdot(2\mathbin{\mathrm{xor}}1)=0\) in \(\mathbb F_2\). Since \(a\ne b\), this forces \(a\mathbin{\mathrm{xor}}b=3\). Directly retaining the original Walsh coefficients then gives
\[
 \mathcal H_{2,1}=-\mathcal H_{3,0}=:-H,
 \qquad \|H\|^2=1/8.
 \tag{4.5}
\]
Indeed \(H\) has only child outputs \(\{0,3\},\{1,2\}\); each of its eight nonzero entries has magnitude \(1/8\), and its two rows are proportional. This proves the norm assertion without a floating eigenvalue calculation.

The actual row-identified residual therefore has the exact positive square
\[
 \boxed{\quad R_{\rm eq}=[-d_0H,d_1H],\qquad
 R_{\rm eq}^*R_{\rm eq}
  =2\operatorname{diag}(d_0^2H^*H,d_1^2H^*H)
        -[d_0I,d_1I]^*H^*H[d_0I,d_1I].\quad}
 \tag{4.6}
\]
The negative square is part of the exact positive Gram. In particular the norm of its symmetrized matching-cycle term is \(|\kappa_0\kappa_1|/8\), not twice this. The matching masks remain different original flag states after row equality.

This also gives a precise obstruction to transporting only the primitive pair coefficient Gram and a scalar child allowance. Take
\[
 a_0=a_1=3/5,\quad b_0=4/5,\quad b_1=-4/5,
 \qquad d_0=12/25,\quad d_1=-12/25.
 \tag{4.7}
\]
At the primitive interface the same projected two-creation residual is the row \([d_0,d_1]\) times the common unitary. It kills the legitimate coherent matching input \((|B_0\rangle+|B_1\rangle)/\sqrt2\). In the actual consumed model after the specified row equality, (4.6) sends that input to \(-\sqrt2(12/25)H\), and hence its squared norm, optimized only over the retained row vector, is
\[
 \boxed{\qquad 2(12/25)^2\|H\|^2=36/625>0.\qquad}
 \tag{4.8}
\]
Therefore no scalar multiple of that primitive pair Gram can dominate this row-identified consumed Gram: a zero quadratic form on this input would remain zero. The failure is specifically the erasure of the distinct-pair child cross in (4.3). It is not a failure of row equality itself, which is an isometry and preserves the actual full positive Gram by congruence. No original edge variables were identified to produce the example.

## 5. Scope, costs, and checks

The transfer assumes (1.1), the explicit projection orbit (1.2), and actual hard-core original labels. Its general consumed inequalities additionally assume flat \(B\). Equation (2.8) is exact only at child vacuum with all rows; row restriction gives its stated upper bound. Equations (4.5)--(4.8) use the specified four-label Walsh transforms and actual row equality. These hypotheses are supplied properties of the input, not conclusions inferred from desired estimates.

The retained objects are the full/empty/half-rung masks, the ordered lowering maps, and the actual \(Z_i^*Z_l\) or \(F_{ba}^*F_{dc}\). A common right boundary map preserves their positive block budgets by congruence; it must be applied to the complete input interfaces. Transporting a scalar cross norm through both endpoints instead requires the corresponding boundary norms. Original-variable identification changes the flag algebra. A common left output change requires the newly compressed shared Gram.

The collective coefficient block has \(\binom Mq\) input and \(\binom M{q-1}\) output occupations; the closed equal-weight norm and the scalar bound (1.6) avoid this enumeration. Exact evaluation of weighted blocks, positive-child-grade Grams, row identifications, represented boundary vectors, and arithmetic precision has its actual cost. No economical general moment algorithm is asserted.

The [companion verifier](verify_cycle_transfer.py) and [report](cycle_transfer_checks.json) record 28 exact equalities, 15 exact Schur positivity checks, and one nonzero control. They construct original primitive crosses on two and four half-rungs, check all their nonzero layer grades and an unequal-weight Boolean allowance, and construct the actual four-label consumed crosses at child grades zero and one with full/restricted rows. The chronological two-creation residual is assembled from original edge/child paths before comparison with (4.3), actual row equality, and (4.6)--(4.8). Arithmetic is rational throughout. Only basic matrix helpers are loaded from the earlier verifier, without running its suite; the report pins that dependency as well as this proof and its own script. The finite fixtures use the displayed real marks and Walsh transforms; general complex transforms and arbitrary positive child grades are analytical proof coverage, not sampled claims.

These checks supplement the analytic proof, not an enumeration of the independent sign law. The established fact that coefficient or phase summaries can fail under continuation is not claimed as new; the contribution here is the exact collective half-rung transfer and the same-square positive child-Gram rule. No sampling theorem, full arbitrary-support creator theorem, graph-separator theorem, MI-32 solution, or novelty claim follows from this note.
