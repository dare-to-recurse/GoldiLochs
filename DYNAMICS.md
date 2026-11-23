# Dynamics of the selected finite tails

These reductions use published results about continued fractions and geodesic flow. The dynamical conclusions below are conventional and have not been formalized in Lean.

## A bounded observable on the exact geodesic segment

Write \(x_n=V_n/U_n\). Take \(X=\Gamma\backslash G\) with \(G=\operatorname{PGL}_2(\mathbb R)\) and \(\Gamma=\operatorname{PGL}_2(\mathbb Z)\), and use the right actions

\[
u_x=\begin{pmatrix}1&x\\0&1\end{pmatrix},
\qquad a(t)=\operatorname{diag}(e^{-t/2},e^{t/2}).
\]

For the reduced rational \(x_n\), consider the time-weighted measure

\[
\mu_n=\frac{1}{2\log U_n}\int_0^{2\log U_n}
\delta_{\Gamma u_{x_n}a(t)}\,dt.
\]

David and Shapira use a cross section \(\Sigma\) for this flow. Fix their thickening width \(r_*=\frac12\inf_\Sigma r_\Sigma>0\), where \(r_\Sigma\) is the first return time, and put \(F=r_*^{-1}\mathbf 1_{\Sigma a((0,r_*))}\). Lemma 4.9 with \(f=1\) gives an error less than \(2/\log U_n\) between \(\mu_n(F)\) and \(\tau_n/(2\log U_n)\). Its rational hypotheses are \(U_n>2\) and \(V_n\notin\{1,U_n-1\}\). The height scale gives \(U_n=Q_n^{1/2+o(1)}\), and \(V_n\leq U_n/2\) rules out \(U_n-1\) eventually. The moving-center result at center zero rules out \(V_n=1\) eventually. The Haar-null boundary calculation in Lemma 4.11 and the normalization \(\kappa=3/\pi^2\) in Theorem 4.12 give \(\mu_{\mathrm{Haar}}(F)=6\log(2)/\pi^2\). Thus the limit of this single bounded observable is equivalent to the tail law. Weak convergence of the full time-weighted measures to Haar would suffice. [David and Shapira, *Equidistribution of divergent orbits and continued fraction expansion of rationals*, §4](https://arxiv.org/pdf/1707.00427)

Their Theorem 1.7 uses sets \(\Lambda_q\) of reduced numerators with \(\log|\Lambda_q|/\log q\to1\) and no escape of mass. A singleton has log-cardinality zero. Time translation of an individual segment yields asymptotic diagonal invariance as \(\log U_n\to\infty\), which still admits invariant measures on closed geodesics. The paper's equation (5) also splits a segment at \(\log U_n\) into two initial half-segments, one for \(V_n\) and one for the negative inverse \(V'_n\bmod U_n\), related by lattice duality. If \(h_n=Q_n/d_n\), Fibonacci reconstruction gives \(h_n V'_n\equiv-F_{k_n-1}\pmod{U_n}\). Controlling the half-segments still requires a result about these specific residues. [David and Shapira, Theorem 1.7 and §2.1](https://arxiv.org/pdf/1707.00427)

The Hecke-neighbor result of Aka and Cohen supplies chosen windows along a density-one set under a positive-entropy hypothesis on the initial orbit limit set. Their Example 1.7 treats the golden-ratio closed geodesic at zero entropy. The prescribed finite segments above are outside the window conclusion. [Aka and Cohen, *Equidistribution of Hecke neighbours and continued fraction patterns*, Theorem 1.4, Corollary 1.6 and Example 1.7](https://arxiv.org/abs/2611.15558)

## Continued-fraction cylinders at the selected residue

A sufficient shadowing statement would give a common prefix of length \(m_n\) with continuant \(P_n\) for \(x_n\) and a comparison orbit, such that

\[
\frac{\log P_n}{m_n}\longrightarrow \frac{\pi^2}{12\log 2},
\qquad
\frac{\log P_n}{\log U_n}\longrightarrow 1.
\]

The unshared suffix of length \(\tau_n-m_n\) has continuant at least \(F_{\tau_n-m_n+1}\). The product of the two continuants is at most \(U_n\), by multiplying the two continued-fraction matrices. Hence \(\tau_n-m_n=O(1+\log(U_n/P_n))=o(\log U_n)\). The length rate then follows. Finding a Gauss-generic irrational in each matching cylinder gives its asymptotic statistics at that point. The argument here requires control of the finite prefix of length \(m_n\).

The cylinder condition has a useful resolution in the original integer \(v_n\). Set \(f_n=F_{k_n}\), \(\rho_n=F_{k_n-1}/f_n\), and \(R_n=v_n f_n/Q_n\). Reconstruction yields \(R_n=x_n/(1+\rho_n x_n)\), whose derivative in \(x_n\) lies between \(4/9\) and \(1\) for \(0\le x_n\le 1/2\). A cylinder of continuant \(P\) has width between \(1/(2P^2)\) and \(1/P^2\). Its intersection with the admissible \(x_n\)-range therefore pulls back to an interval of width \(O((Q_n/f_n)P^{-2})\) in \(v_n\). The scale estimates give \(Q_n/f_n=U_n^{1+o(1)}\). At \(P\ge U_n^{1-\eta}\) for fixed \(\eta<1/2\), the interval has width \(o(1)\), even before the congruence for \(v_n\) is imposed. Applying an ensemble theorem at this resolution requires a separate estimate that places the selected residue in the good cylinders.

## Weak Gauss statistics with an exceptional last quotient

Choose a Gauss-generic transcendental \(y=[0;a_1,a_2,\ldots]\) with convergent denominators \(P_m\) satisfying \(\log P_m/m\to \pi^2/(12\log 2)\) and \(a_{j+1}\le C P_j\) for all \(j\ge0\), where \(P_0=1\) and \(C\ge1\) is fixed for that \(y\). Such \(y\) have full Gauss measure by the ergodic theorem, the countability of algebraic numbers, and the Gauss tail estimate \(\mu(a_1>H)=O(1/H)\). For the last inequality use \(P_j\ge F_{j+1}\), the Borel–Cantelli lemma, and enlarge \(C\) to cover the finite exceptions. The logarithmic denominator rate follows from the Gauss mean of \(-\log x\), since \(\prod_{i=0}^{m-1}T^i y=1/(P_m+P_{m-1} T^m y)\).

Form \(z_m=[0;a_1,\ldots,a_m,P_m]\) for sufficiently large \(m\). Its height is \(U=P_m^2+P_{m-1}\) and its canonical length is \(m+1\), so its length divided by \(\log U\) tends to \(6\log(2)/\pi^2\), half the desired tail rate. Yet the empirical Gauss measures converge weakly to the Gauss measure. For fixed \(J\), the orbits of \(y\) and \(z_m\) share the next \(J\) digits at every index \(i\le m-J\), and the corresponding points are at distance at most \(F_{J+1}^{-2}\). Compare continuous observables using uniform continuity, discard the last \(J+1\) indices, and then let \(J\to\infty\). The single last ratio \(1/P_m\) contributes \(\log P_m\) to the logarithmic sum.

These synthetic rationals also satisfy \(q^4|z_m-p/q|\gg1\) uniformly over distinct reduced rationals \(p/q\). When the difference is at least \(1/(2q^2)\), this is immediate. Otherwise Legendre's theorem makes \(p/q\) a convergent. A proper canonical convergent of denominator \(q\) satisfies \(|z_m-p/q|\ge 1/((a_{\rm next}+2)q^2)\) by the continuant determinant formula. The next coefficient is at most \(Cq\), including when it is the appended \(P_m\). If using the alternative expansion ending in \(1\), the one additional proper convergent has denominator \(U-P_m\ge U/2\) for large \(m\), and \(|z_m-p/q|\ge1/(Uq)\) suffices. These examples meet the moving-center avoidance strength and weak Gauss statistics simultaneously while failing the proposed normalized length law. [Mathlib's real Legendre theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/DiophantineApproximation/Basic.html#Real.exists_rat_eq_convergent)

The same construction can avoid fixed algebraic centers when read in reverse. Append the reverse of the first \(\lfloor\sqrt m\rfloor\) digits of a fixed transcendental number with digits in \(\{2,3\}\). The reversed expansion begins with a growing prefix of that number. The extra digits contribute \(o(m)\) to the length and log height, so the normalized length and weak Gauss limits stay the same. Each new digit is bounded, so the fourth-power-weighted approximation estimate still applies. The large quotient now lies inside the trajectory, before the short suffix.

For the actual decimal tails, a proof by discrete Gauss averages still needs both finite-orbit statistics and control of the total contribution of ratios near zero. The flow formulation instead asks for the limiting occupation of the fixed thickened section on the exact individual segments.

## Fixed algebraic centers of the reversed tail

Write the original decimal fraction in lowest terms as \(p/q=A_n/Q_n\), and take its penultimate convergent \(p'/q'\) with \(pq'-qp'=\sigma\in\{-1,1\}\). The denominator \(q\) tends to infinity, is supported on \(2,5\), and satisfies \(|p-\phi q|\le 1\). For every fixed real algebraic \(t\) and every \(\eta>1/2\), eventually
\[
|q'/q-t|>q^{-\eta}.
\]
It suffices to treat \(1/2<\eta<1\). Put \(r=p/q\), \(s=q'/q\), and suppose \(|s-t|\le q^{-\eta}\) infinitely often.

For \(Y=(q,p,q',p')\), take the four archimedean linear forms with values
\[
q,\quad p-\phi q,\quad q'-tq,\quad
p'-\phi q'-t(p-\phi q)=(p-\phi q)(s-t)-\sigma/q.
\]
They are independent, and their magnitudes are respectively \(q,O(1),O(q^{1-\eta}),O(q^{-\eta})\). The Subspace Theorem is used in a normal number field containing the real algebraic coefficients, with all archimedean places and the places over \(2,5\). At each archimedean place choose coefficient preimages under its embedding, so the evaluated forms equal the displayed values. Use coordinate forms at finite places. The factors of \(q\) cancel by the product formula, all remaining finite factors are at most one, and the local coordinate maximum outside the chosen places is one. The projective height is \(O(q)\), while the product after cancellation is \(O(q^{1-2\eta})\). Thus the exceptional vectors belong to finitely many proper linear subspaces. A vanishing form itself gives a proper subspace. Since the vectors have rational coordinates, any recurring subspace yields a fixed nonzero relation over \(\mathbb Q\) by expansion in a field basis.

Write this relation as \(a q+b p+c q'+d p'=0\). Taking limits after dividing by \(q\) shows \(a+b\phi+c t+d\phi t=0\). If \(c=d=0\) then \(a=b=0\), so \(c+d\phi\ne0\). The determinant relation gives
\[
s=F(r)+\frac{d\sigma}{q^2(c+d r)},\qquad F(r)=-\frac{a+b r}{c+d r},\qquad F(\phi)=t.
\]
Taylor expansion and \(|r-\phi|\le q^{-1}\) give \(q'-tq-F'(\phi)(p-\phi q)=O(q^{-1})\). Apply the same argument to \((q,p,q')\), using \(q,p-\phi q,q'-tq-F'(\phi)(p-\phi q)\). After \(q\) cancels the product is \(O(q^{-1})\), so a further recurring rational relation yields \(Dq'=Aq+Bp\) with fixed integers \(D\ne0,A,B\). Here \(B\ne0\), since \(B=0\) would make the reduced fraction \(q'/q\) constant while \(q\to\infty\).

The determinant then gives \(B(p^2-pq-q^2)=D\sigma+j_n q\) with integers \(j_n\). They are bounded because \(|p-\phi q|\le1\) and \(p^2-pq-q^2=(p-\phi q)(p-\phi' q)\), where \(\phi'=(1-\sqrt 5)/2\). Pass to a fixed \(j_n=j\). It follows that \(p-\phi q=\lambda+O(q^{-1})\), where \(\lambda=j/(B\sqrt5)\). A third application to \((q,p,1)\), using \(q,1,p-\phi q-\lambda\) at the archimedean places, gives a recurring rational relation \(e q+f p+g=0\). Taking limits gives \(e+f\phi=0\), hence \(e=f=0\) and then \(g=0\), a contradiction. These applications use the projective inequality in equation (2.11). [Evertse and Schlickewei, *The Absolute Subspace Theorem*](https://pub.math.leidenuniv.nl/~evertsejh/98-absolute.pdf)

For the residual fraction \(x=V_n/U_n\), let \(a/b\) be its penultimate convergent, using \(0/1\) if it has one quotient after the initial zero. Prefix reconstruction gives \(q=F_{k_n}U_n+F_{k_n-1}V_n\) and \(q'=F_{k_n}b+F_{k_n-1}a\). Its determinant gives
\[
|q'/q-b/U_n|=\frac{F_{k_n-1}}{qU_n}\le U_n^{-2}.
\]
The ratio \(b/U_n\) has the reversed residual quotients by transposing their symmetric continued-fraction matrices. Its expansion is canonical because the first forward residual quotient is at least two. With the logarithmic scales from Ridout's theorem, \(q=Q_n^{1+o(1)}\) and \(U_n=Q_n^{1/2+o(1)}\). Hence eventually \(|b/U_n-t|>Q_n^{-\theta}\) for every \(\theta>1/2\): choose \(1/2<\eta<\min(\theta,1)\) in the original bound, and use the \(U_n^{-2}\) error. The proof treats equality with a center as well. A fixed rational center can equal the reduced fraction \(q'/q\) only at its fixed denominator, and an irrational one never equals it.

A fixed pattern repeated for \(m\) digits immediately before a fixed terminal word in the forward tail becomes an eventually periodic cylinder of the reverse expansion. The cylinder has a fixed quadratic irrational center obtained by repeating the pattern forever. If the repeat has per-digit continuant growth factor \(\rho>1\), the distance to that center is \(O(\rho^{-2m})\). Thus along any infinite such subsequence one must have \(\limsup m/n\le \log(10)/(4\log\rho)\). One may take \(\rho=\phi\) in the universal estimate from Fibonacci growth. This argument still leaves shorter terminal blocks and the entire orbit mean undetermined.

### Strengthening to every positive exponent

In fact \( |q'/q-t|>q^{-\epsilon}\) eventually for every fixed real algebraic \(t\) and every \(\epsilon>0\). To prove it, first note an inhomogeneous consequence of the same Subspace Theorem. For each fixed real algebraic \(\lambda\) and each \(\xi>0\), the inequality \(|p-\phi q-\lambda|\le q^{-\xi}\) holds only finitely often. Indeed, the application to \((q,p,1)\) above works with any such \(\lambda\), since the product after canceling \(q\) is \(O(q^{-\xi})\). Thus if \(\Delta=p-\phi q\) and \(L\) is a fixed nonzero polynomial with real algebraic coefficients, then \(|L(\Delta)|>q^{-\xi}\) eventually for each \(\xi>0\). Factor \(L\) over \(\mathbb C\) and apply the inhomogeneous inequality to its real roots with a smaller exponent divided by the degree. The nonreal roots stay at a fixed positive distance from the real \(\Delta\).

Suppose \(|s-t|\le q^{-\epsilon}\) infinitely often, where \(s=q'/q\) and \(0<\epsilon<1\). Set
\[
f=q'-tq,\qquad g=p'-\phi q'-t(p-\phi q).
\]
Then \(\Delta=O(1)\), \(f=O(q^{1-\epsilon})\), \(g=O(q^{-\epsilon})\), and \(\Delta f-qg=\sigma\). Choose a fixed integer \(d\ge2\) with \((d+1)\epsilon>1\). Use an integer vector with coordinates
\[
\begin{split}
X_i&=q^{d-i}p^i &&(0\le i\le d),\\
Y_0&=q^{d-1}q',&
Y_i&=q^{d-i}p^{i-1}p' &&(1\le i\le d),\\
Z_i&=\sigma q^{d-2-i}p^i &&(0\le i\le d-2).
\end{split}
\]
As polynomials in the four entries of the convergent matrix, these form a basis of the homogeneous degree-\(d\) polynomials of degree at most one in \((q',p')\). Indeed, the \(Z_i\) use \(\sigma=pq'-qp'\), and together with the \(Y_i\) they recover all degree-\(d\) monomials with exactly one factor from \((q',p')\). The substitution \((q,p,q',p')\mapsto(q,\Delta,f,g)\) is invertible, preserves this polynomial space and preserves the determinant. Therefore the analogous polynomials in \((q,\Delta,f,g)\) are independent linear forms on the chosen vector coordinates.

Use these transformed forms at each archimedean place, with coefficient preimages as above, and use coordinate forms at the finite places over \(2,5\). The archimedean powers in the \(X_i,Y_i\) product sum to
\[
\sum_{i=0}^d(d-i)+(d-\epsilon)+\sum_{i=1}^d(d-i-\epsilon)
=d(d+1)-(d+1)\epsilon.
\]
The displayed factors of \(q\) in those integer coordinates have total exponent \(d(d+1)-1\). Their finite contributions cancel that much of the archimedean exponent. Each \(Z_i\) has archimedean bound \(O(q^{d-2-i})\) and its specified finite \(q\)-factor cancels that power. Every remaining finite factor is at most one. Thus the product is \(O(q^{1-(d+1)\epsilon})\). The height is \(O(q^d)\), and the coordinate \(X_0=q^d\) guarantees local maximum one outside the chosen places. The Subspace Theorem again forces a recurring rational linear relation.

Divide that relation by \(q^d\) and substitute \(p'/q=rs-\sigma/q^2\), where \(r=p/q\). The result is
\[
P(r)+sR(r)+\sigma q^{-2}S(r)=0
\]
for rational polynomials \(P,R,S\) that are not all zero. This follows directly from the coordinate definitions: the \(X_i\) supply the coefficients of \(P\), the \(Y_i\) those of \(R\), and the \(Z_i\) the remaining coefficients of \(S\). Pass to a subsequence with fixed \(\sigma\). For a polynomial \(T\), let \(\nu(T)\) be its order of vanishing at \(\phi\), with \(\nu(0)=+\infty\). Put \(m=\min\{\nu(P),\nu(R),2+\nu(S)\}\). Multiply the relation by \(q^m\) and expand in \(r-\phi=\Delta/q\). The leading polynomial in \(\Delta\) is the sum of the following terms, with a term included only when its stated condition holds:

- The leading Taylor coefficient of \(P\) times \(\Delta^m\), if \(\nu(P)=m\).
- The leading Taylor coefficient of \(R\) times \(t\Delta^m\), if \(\nu(R)=m\).
- The leading Taylor coefficient of \(S\) times \(\sigma\Delta^{m-2}\), if \(2+\nu(S)=m\).

The error is \(O(q^{-\min(1,\epsilon)})\) because \(\Delta\) is bounded and \(s=t+O(q^{-\epsilon})\). The leading polynomial therefore vanishes identically by the inhomogeneous consequence. Its last possible term has distinct degree and nonzero coefficient, so \(2+\nu(S)>m\). Also \(\nu(R)=m\), since otherwise the first term would be the sole nonzero term. Now \(F=-P/R\) has a removable singularity at \(\phi\), and \(S/R=O(1+|r-\phi|^{-1})\) near \(\phi\). Using \(|\Delta|>q^{-\xi}\) gives
\[
s=F(r)+O(q^{-1+\xi})=F(\phi)+O(q^{-1+\xi})
\]
for every fixed \(\xi>0\). Thus \(F(\phi)=t\) and \(s-t=O(q^{-7/8})\), which contradicts the already proved bound at exponent \(3/4\). [Evertse and Schlickewei, *The Absolute Subspace Theorem*, equation (2.11)](https://pub.math.leidenuniv.nl/~evertsejh/98-absolute.pdf)

The \(U_n^{-2}\) comparison and the logarithmic scales now give \(|b/U_n-t|>Q_n^{-\epsilon}\) eventually for every \(\epsilon>0\). With \(t=0\), this implies \(\log a_{\rm last}/\log Q_n\to0\), since \(a_{\rm last}b\le U_n\). For an eventually periodic reverse center, every positive linear number of repetitions of a fixed pattern would give exponential proximity. Such a terminal block therefore has \(o(n)\) digits for each fixed terminal word and fixed repeated pattern. This does not control large quotients deep inside the trajectory.

The weak-statistics example with a transcendental suffix given above is compatible with both endpoint exclusions. Its large interior quotient still prevents the target length rate.
