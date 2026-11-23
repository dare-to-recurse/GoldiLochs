# A Diophantine bound for the start of the residual tail

This conventional proof uses the number-field Subspace Theorem and remains to be formalized in Lean. It addresses the arithmetic and refutation routes described in PROMPT.txt.

## Phase identity and approximation statement

Use the notation of PROMPT.txt and suppress the index \(n\). Let \(x=V/U=v/u\) and \(w=\phi^{-2k}\). For every \(0<\epsilon\le 1\), for all sufficiently large \(n\) and every reduced rational \(p/q\in[0,1]\) with \(1\le q\le Q^{\epsilon/24}\), we have

$$
|x-p/q|>Q^{-\epsilon}.
$$

For \(n\ge 1\), \(A>Q\) follows from \(Q\ge 10\) and \(\phi>3/2\). Every Euclidean pair after a step with positive second entry has first entry strictly greater than its second entry. A quotient of one at such a pair leaves a positive remainder, so removing the initial run of ones leaves \(u\ge 2v>0\). The fractional part \(\delta=\phi Q-A\) satisfies \(0<\delta<1\) by irrationality. The nonzero integer \(A^2-AQ-Q^2=-\delta(\sqrt5 Q-\delta)\) also gives \(\delta\ge 1/(\sqrt5 Q)\).

During a step with quotient one, \((a,b)\mapsto(b,a-b)\) multiplies \(a-\phi b\) by \(-\phi\) and \(a+b/\phi\) by \(\phi^{-1}\). The first expression starts negative and ends positive, since \(u\ge 2v>0\) and \(\phi<2\). Thus \(k\) is odd, and

$$
z(x):=\frac{1-\phi x}{1+x/\phi}
 =\frac{u-\phi v}{u+v/\phi}
 =\frac{\phi^{2k}\delta}{\sqrt5 Q-\delta}.
$$

On \(0<x\le 1/2\), one has \(\phi^{-4}\le z(x)<1\). In particular,

$$
w=\frac{\delta}{z(x)(\sqrt5 Q-\delta)},\qquad
\frac{1}{5Q^2}\le w\le \frac{C_0}{Q}
$$

for an absolute constant \(C_0\). The function \(z(t)=(1-\phi t)/(1+t/\phi)\) is Lipschitz on \([0,1]\). For \(t\) in this interval,

$$
\delta-\sqrt5\,z(t)Qw
=\sqrt5\,Qw\bigl(z(x)-z(t)\bigr)-z(x)\delta w
=O\bigl(|x-t|+w\bigr).
$$

## Subspace Theorem

Take \(K=\mathbb Q(\sqrt5)\) and let \(S\) consist of its two real places and the finite places over 2 and 5. Write a prime for conjugation in \(K\), so that \(\phi'=-1/\phi\) and \(w'=w^{-1}\). Use product-formula-normalized absolute values, giving \(|a|_\pm=|\sigma_\pm(a)|^{1/2}\) at the real places. Put \(\|y\|_v=\max_i|y_i|_v\) and \(H(y)=\prod_v\|y\|_v\).

For each \(v\in S\), prescribe \(m\) linearly independent \(K\)-linear forms in \(m\) variables. For any \(\eta>0\), the vectors satisfying

$$
\prod_{v\in S}\prod_{i=1}^m
\frac{|L_{v,i}(y)|_v}{\|y\|_v}
\le H(y)^{-m-\eta}
$$

lie in finitely many proper \(K\)-linear subspaces. This is the qualitative formulation in equation (2.11), with the local-degree weights absorbed into the absolute values. The vanishing of any chosen form gives a proper subspace directly. When \(\|y\|_v=1\) outside \(S\), the required bound on the product of the unscaled form values is \(H(y)^{-\eta}\). [Evertse and Schlickewei, *The Absolute Subspace Theorem*, §2](https://pub.math.leidenuniv.nl/~evertsejh/98-absolute.pdf)

### Fixed centers

For each fixed \(t\in K\cap[0,1]\) and \(0<\epsilon\le 1\), the inequality \(|x-t|\le Q^{-\epsilon}\) has only finitely many indices. Take \(y=(Q,A,Qw)\). At \(\sigma_+\) use \(X_1,X_3,\phi X_1-X_2-\sqrt5 z(t)X_3\). At \(\sigma_-\) use \(X_1,X_3,\phi' X_1-X_2\). The last form at this latter place evaluates, after applying \(\sigma_-\), to \(\delta\). At every finite place of \(S\) use the coordinate forms. Each collection is linearly independent.

The coordinates \(Q,Qw\) are \(S\)-units and their form values contribute a total factor of one by the product formula. The finite-place contributions from \(A\) are at most one. The two remaining real form values contribute \(O(Q^{-\epsilon/2})\) jointly, using the phase identity and \(0<\delta<1\). All coordinates are integral and \(Q\) is a unit outside \(S\), so \(\|y\|_v=1\) there. The real maximum coordinate is \(O(Q)\) at \(\sigma_+\) and \(O(Q^3)\) at \(\sigma_-\), giving \(H(y)=O(Q^2)\). This verifies the theorem with any fixed \(0<\eta<\epsilon/4\) for sufficiently large \(n\).

If infinitely many indices satisfied the approximation, a recurring proper subspace would give \(\lambda_1+\lambda_2 A/Q+\lambda_3 w=0\) with fixed coefficients in \(K\) not all zero. Taking limits gives \(\lambda_1+\lambda_2\phi=0\). If \(\lambda_3=0\), the original relation implies \(\lambda_2\delta=0\), forcing all coefficients to vanish. If \(\lambda_3\ne 0\), conjugation produces the unbounded term \(\lambda_3'/w\) alongside bounded terms, also impossible.

### Moving rational centers

Suppose \(|x-p/q|\le Q^{-\epsilon}\) with \(0<p\le q\le Q^{\epsilon/24}\), \(\gcd(p,q)=1\), for infinitely many \(n\). The fixed-center bound covers \(p=0\). Use

$$
y=(qQ,pQ,qA,pA,qQw,pQw).
$$

At each real place retain \(X_1,X_2,X_5,X_6\). At \(\sigma_+\), add

$$
\phi X_1+X_2-X_3-\phi^{-1}X_4-\sqrt5 X_5+\sqrt5\phi X_6,
\qquad \phi X_2-X_4.
$$

Their values are \(E=(q+p/\phi)(\delta-\sqrt5 z(p/q)Qw)=O(q Q^{-\epsilon})\) and \(p\delta\). At \(\sigma_-\), add \(\phi'X_1-X_3\) and \(\phi'X_2-X_4\), with values \(q\delta,p\delta\) after applying \(\sigma_-\). Use the six coordinate forms at the finite places in \(S\). The added forms at each real place have independent coefficients on \(X_3,X_4\).

The product of the four retained coordinate factors across \(S\) is at most \((pq)^2\). The \(S\)-units \(Q,Qw\) contribute one. For a natural number \(m\) with \(m>0\), the product over all finite places of \(|m|_v\) is \(1/m\), so \(\prod_{v\in S}|m|_v\le m\). The two additional forms at each real place contribute \(O(q^2 Q^{-\epsilon/2})\) jointly. The two remaining finite-place coordinate factors have absolute value at most one by integrality. The product of all unscaled form values therefore satisfies

$$
O(q^6 Q^{-\epsilon/2})=O(Q^{-\epsilon/4}).
$$

Coprimality ensures that at each finite place outside \(S\), \(qQ\) or \(pQ\) is a unit, so \(\|y\|_v=1\). The real maximum coordinate bounds give \(H(y)=O(qQ^2)\). With \(\eta=\epsilon/16\), these estimates imply the required Subspace Theorem inequality for sufficiently large \(n\).

One recurring subspace gives a relation with fixed \(a,b,c,d,e,f\in K\), not all zero:

$$
(aq+bp)+(cq+dp)A/Q+(eq+fp)w=0.
$$

It follows that \(R=(a+\phi c)q+(b+\phi d)p=O(q/Q)\). A nonzero value of a fixed form \(gq+hp\), with \(g,h\in K\) and \(p\le q\), has absolute value at least \(c_{g,h}/q\) for some \(c_{g,h}>0\). To see this, multiply by a fixed integer to make the coefficients integral, take the nonzero integer field norm, and bound the conjugate by \(O(q)\). Since \(q^2/Q\to0\), the form \(R\) vanishes for every sufficiently late index in the subspace. If its coefficients are not both zero, \(p/q\) is fixed, contradicting the fixed-center bound.

When the coefficients of \(R\) are both zero, the relation reads \((eq+fp)w=(cq+dp)\delta/Q\). Conjugation gives \(|e'q+f'p|=O(qw)=O(q/Q)\) because \(\delta'/Q=\phi'-A/Q\) is bounded. The same norm bound implies \(eq+fp=0\) eventually. Then \(cq+dp=0\) by \(\delta>0\). At least one of these forms has nonzero coefficients. It again fixes \(p/q\), completing the contradiction.

## Consequences for the tail

Taking \(t=0\) gives \(\log(V/U)=o(\log Q)\). With the conventional height scale \(\log U/\log Q\to 1/2\) from Ridout's theorem and the finite split, this implies \(\log V/\log Q\to1/2\).

Under the same height scale, write the canonical expansion as \(x=[0;b_1,\ldots,b_\tau]\), where \(\tau=E(U,V)\). For each fixed \(j\ge1\), the digit \(b_j\) eventually exists and \(\log b_j/\log Q\to0\). Inductively the preceding convergent has denominator \(q_{j-1}=Q^{o(1)}\), by the continuant recurrence (the initial convergent is \(0/1\)). It cannot equal \(x\) for infinitely many indices because \(x\) in lowest terms has denominator \(U=Q^{1/2+o(1)}\). If \(b_j\ge Q^\epsilon\) along an infinite subsequence for some \(0<\epsilon\le1\), the convergent error bound

$$
\left|x-\frac{p_{j-1}}{q_{j-1}}\right|
\le \frac{1}{b_j q_{j-1}^2}
$$

contradicts the moving-center result, since \(q_{j-1}\le Q^{\epsilon/24}\) eventually. This gives \(\tau_n\to\infty\). The argument controls a fixed number of coefficients and excludes a single exponentially large coefficient preceded by a convergent of subexponential height. The approximation threshold depends on the height of the center. The required limit concerns the entire trajectory, including convergents with denominators comparable to powers of \(Q\). The aggregate mean and the limit of \(\tau_n/n\) remain unresolved.

### A family illustrating the remaining gap

The height scales and approximation bounds above permit different tail depths in families of rational numbers. For example, use \(a=2\) at even indices, \(a=3\) at odd indices, and let \(\rho_a=(a+\sqrt{a^2+4})/2\). Define \(x_n\) for this example by a continued fraction with integer part zero and \(m_n=\lfloor\log Q/(2\log\rho_a)\rfloor\) copies of \(a\), for all sufficiently large \(n\). The denominator recurrence \(q_m=a q_{m-1}+q_{m-2}\) gives \(q_{m_n}\) between two fixed positive multiples of \(\sqrt Q\). The same height scale holds for the numerator, since \(x_n\) approaches \(1/\rho_a>0\) along each parity. The continued fraction is canonical and has \(m_n\) coefficients after the integer part. Its normalized depth \(m_n/\log q_{m_n}\) tends to \(1/\log\rho_a\) along the corresponding parity, giving two distinct limits.

These examples satisfy the same approximation bounds. For \(p/q\in[0,1]\), the integer \(p^2+apq-q^2\) is nonzero, giving \(|p/q-1/\rho_a|\ge ((a+2)q^2)^{-1}\) by the mean value theorem applied to \(t^2+at-1\). At the same time, \(|x_n-1/\rho_a|=O(Q^{-1})\) by the continued-fraction convergent estimate. When \(q\le Q^{\epsilon/24}\), these inequalities give \(|x_n-p/q|>Q^{-\epsilon}\) eventually. Each \(1/\rho_a\) lies outside \(\mathbb Q(\sqrt5)\), so proximity to a fixed center in that field is also excluded.

This example concerns the logical strength of the approximation and scale statements. The specified decimal truncations additionally prescribe \(x_n\) by the phase identity and the numerator \(A_n=\lfloor\phi Q_n\rfloor\). A tail limit argument still needs information from this selection rule or further properties of its Euclidean trajectories.
