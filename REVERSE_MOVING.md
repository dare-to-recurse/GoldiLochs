# Moving rational centers of the reverse expansion

The number-field Subspace Theorem arguments in this note are conventional proofs. Only the finite determinant and Euclidean estimates have been checked in Lean. The mean of the complete selected tail remains unresolved.

## Notation and statement

Let \(p/q\) be the original reduced decimal truncation and \(p'/q'\) its penultimate convergent. Use
\[
r=p/q,\qquad s=q'/q,\qquad \Delta=p-\phi q,\qquad \sigma=pq'-qp'=\pm1.
\]
The integer \(q\) tends to infinity and has prime factors only \(2,5\). We have \(|\Delta|\le1\), \(r-\phi=\Delta/q\), and \(p'/q=rs-\sigma/q^2\). For a reduced rational center \(t=A/B\in[0,1]\), the bound is
\[
|s-t|>q^{-\epsilon}
\quad\text{eventually for all }1\le B\le q^\beta,
\qquad 0<\epsilon\le1,\quad 0<\beta<\min(\epsilon/4,1/7).
\tag{1}
\]
No scale hypothesis is needed for this assertion about \(s\). The degree of the polynomial lift below can depend on \(\epsilon,\beta\).

Two consequences of [the fixed-center argument](DYNAMICS.md#fixed-algebraic-centers-of-the-reversed-tail) will be used. For each fixed real algebraic \(t\) and each \(\epsilon>0\), \(|s-t|>q^{-\epsilon}\) eventually. For any fixed nonzero polynomial \(L\) with real algebraic coefficients, \(|L(\Delta)|>q^{-\gamma}\) eventually for every \(\gamma>0\). In particular \(\Delta\ne0\) and \(|\Delta|^{-1}=q^{o(1)}\).

Suppose (1) fails at infinitely many indices. A fixed center cannot recur infinitely often, so restrict to a subsequence on which the \(t\)'s are distinct and \(A>0\). Every fixed affine expression \(\ell(t)=C+Dt\), with \(C,D\in\mathbb Q(\sqrt5)\) and \(\ell\) nonzero as a polynomial, is eventually nonzero on that subsequence and satisfies \(|\ell(t)|\gg B^{-2}\). Indeed, after clearing the fixed algebraic denominators, the numerator is a nonzero algebraic integer whose conjugate is \(O(B)\). Its norm is a nonzero integer. Dividing the resulting lower bound by \(B\) gives the stated estimate.

In each application below, use a normal number field containing the real form coefficients. Include all archimedean places and the places over \(2,5\). At an archimedean place choose coefficient preimages under the embedding to evaluate the displayed real forms. With product-formula normalization, the archimedean weights sum to one. At the finite places in this set use coordinate forms. Powers of \(q\) explicitly present in the coordinates contribute their reciprocal powers at those finite places. Remaining finite factors are at most one by integrality. Local maxima outside these places equal one, since the vectors contain coordinates \(Aq^j,Bq^j\) for some \(j\ge0\) and \(\gcd(A,B)=1\). A raw form product bounded by a fixed negative power of \(q\), together with height \(q^{O(1)}\), then gives the normalized projective inequality of the Subspace Theorem. Vanishing of any one of the fixed independent forms already gives a proper subspace. Since the vectors have rational entries, a recurring proper subspace gives a nonzero rational relation by expansion in a field basis. [Evertse and Schlickewei, *The Absolute Subspace Theorem*, equation (2.11)](https://pub.math.leidenuniv.nl/~evertsejh/98-absolute.pdf)

## Auxiliary quadratic expression

For fixed \(C,D,E\in\mathbb Q(\sqrt5)\) with \(E\ne0\), put \(H=(C+Dt)\Delta^2+E\). We show that \(H=O(q^{-c})\) cannot hold along the distinct centers when \(c>2\beta\) and \(\beta<1/7\). When \(D=0\), this follows from the fixed-polynomial bound on \(\Delta\). Assume \(D\ne0\).

Take a positive integer \(h\) and the integer coordinates \(Jq^{k-j}p^j\) for \(J=A,B\), even \(0\le k\le2h\), and \(0\le j\le k\). At an archimedean place replace \(p\) by \(\Delta\) in the monomials. For \(j\ge2\), replace each \(Aq^{k-j}\Delta^j\) form by \(Bq^{k-j}\Delta^{j-2}H\). It is \(D\) times the removed form plus terms in the \(B\)-group, since that group contains both the degree \(k\) and degree \(k-2\) monomials. The forms are independent by this replacement and the invertible substitution \(p\mapsto\Delta\). The finite \(q\)-powers cancel the archimedean \(q^{k-j}\) factors. There are \(2(h+1)^2\) forms, and \(h^2\) of them acquire the extra factor \(O(q^{-c})\). Therefore their product is
\[
O\big(B^{2(h+1)^2}q^{-c h^2}\big).
\]
For \(h\) sufficiently large it saves a fixed power of \(q\), since \(2\beta<c\). The height is \(O(Bq^{2h})\).

A recurring rational linear relation, divided by \(Bq^{2h}\), reads
\[
\sum_{j=0}^h q^{-2j}\big(P_j(r)+tR_j(r)\big)=0
\]
with rational polynomials \(P_j,R_j\), some nonzero. For a polynomial \(P\), write \(\nu(P)\) for its order of vanishing at \(\phi\), with \(\nu(0)=+\infty\). Let \(m\) be the least of \(2j+\nu(P_j)\) and \(2j+\nu(R_j)\). Multiplying by \(q^m\) and using \(r=\phi+\Delta/q\) gives
\[
P_*(\Delta)+tR_*(\Delta)=O(q^{-1}).
\]
Here \(P_*,R_*\) consist of the leading terms of the polynomials that attain the minimum. For different \(j\) these terms have distinct degrees \(m-2j\), so \(P_*,R_*\) are not both zero. Eliminate \(t\) using \(H=O(q^{-c})\). The fixed polynomial
\[
(CX^2+E)R_*(X)-DX^2P_*(X)
\]
is \(O(q^{-\min(1,c)})\) at \(X=\Delta\), hence vanishes identically. Since \(D\ne0\), this forces \(R_*\ne0\). Its values at \(\Delta\) have reciprocal \(q^{o(1)}\). Consequently the relation \(P_*+tR_*=O(q^{-1})\) improves the bound to \(H=O(q^{-1+o(1)})\).

Use this improved error in a second application, now to
\[
(Bq^2,Bqp,Bp^2,Aq^2,Aqp,Ap^2,B).
\]
At the archimedean places use \(Jq^2,Jq\Delta,J\Delta^2\) for \(J=B,A\) and \(B\), replacing \(A\Delta^2\) by \(BH\). The forms are independent since \(D\ne0\). This gives product \(O(B^7q^{-1+o(1)})\), which saves because \(\beta<1/7\). The height is \(O(Bq^2)\). A recurring rational relation therefore gives \(P(r)+tR(r)+d_0/q^2=0\) with rational polynomials \(P,R\) of degree at most two and \(d_0\in\mathbb Q\). If \(P=R=0\), then \(d_0=0\), contradicting nontriviality. Otherwise \(m=\min(\nu(P),\nu(R))\le1\), since a nonzero rational polynomial of degree at most two cannot have the irrational quadratic \(\phi\) as a repeated root. Divide by \((r-\phi)^m\). The leading affine expression in \(t\) has error \(O(q^{-1+o(1)})\) and is nonzero as a polynomial. This contradicts its lower bound \(\gg B^{-2}\ge q^{-2\beta}\) up to a fixed positive factor. This proves the auxiliary exclusion.

## Lift for moving centers

For lift degree \(d\ge2\), let \(X_i,Y_i,Z_i\) be the monomials from [the fixed-center lift](DYNAMICS.md#strengthening-to-every-positive-exponent). Use coordinates \(AX_i,BX_i,BY_i,BZ_i\). At the archimedean places use the corresponding forms, with \(p\) replaced by \(\Delta\) and \(Bq',Bp'\) replaced by
\[
F=Bq'-Aq,\qquad G=Bp'-Ap-\phi F.
\]
The transformed pure groups \(AX_i,BX_i\) are independent by the triangular substitution \(p\mapsto\Delta\). Modulo the space spanned by those pure groups, the remaining transformation is the degree-\(d\) change of basis from the fixed-center lift, multiplied by \(B\). In particular \(\Delta F-qG=B\sigma\) and the transformed \(Z_i\) are \(B\sigma q^{d-2-i}\Delta^i\). Thus the entire family is independent.

The assumption \(|s-t|\le q^{-\epsilon}\) implies \(F=O(Bq^{1-\epsilon})\) and \(G=O(Bq^{-\epsilon})\), using \(0<\epsilon\le1\). The extra pure group has canceling archimedean and finite \(q\)-powers. The archimedean bounds acquire a factor \(B\) each, so the fixed-center calculation gives product
\[
O(B^{4d+2}q^{1-(d+1)\epsilon}).
\]
The height is \(O(Bq^d)\), and \(4\beta<\epsilon\) implies saving for sufficiently large fixed \(d\). A recurring rational relation, divided by \(Bq^d\), gives
\[
P(r)+tJ(r)+sR(r)+\sigma q^{-2}S(r)=0.
\tag{2}
\]
The rational polynomials are not all zero. The pure groups supply \(P,J\), the \(Y_i\) supply \(R\), and the \(Z_i\) supply the remaining coefficients of \(S\). Fix \(\sigma\) along the subsequence.

Let \(m=\min(\nu(P),\nu(J),\nu(R),2+\nu(S))\). After multiplying (2) by \(q^m\), the leading terms are \((C+Dt)\Delta^m\), plus \(E\Delta^{m-2}\) with \(E\ne0\) if \(2+\nu(S)=m\). The remaining terms are \(O(q^{-\epsilon})\), since \(s=t+O(q^{-\epsilon})\) and \(\Delta\) is bounded. All leading coefficients lie in \(\mathbb Q(\sqrt5)\). If the \(E\)-term occurs, divide by \(\Delta^{m-2}\) and apply the auxiliary exclusion with \(2\beta<c<\epsilon\), using \(|\Delta|^{-1}=q^{o(1)}\). Hence \(2+\nu(S)>m\). Dividing by \(\Delta^m\) and comparing against the affine norm estimate forces \(C=D=0\). This means \(\nu(P)>m\), \(\nu(J)=\nu(R)=m\), and \(\nu(J+R)>m\). Equation (2) now gives
\[
s-t=-\frac{P(r)+t(J+R)(r)}{R(r)}
      -\frac{\sigma S(r)}{q^2R(r)}
    =O(q^{-1+o(1)}).
\]

Reapply the amplified lift with \(d=1\), no \(Z_i\), and any fixed \(\eta\) satisfying \(1/2+3\beta<\eta<1\). The improved estimate implies \(|s-t|\le q^{-\eta}\) eventually, and the product \(O(B^6q^{1-2\eta})\) saves. In (2) for this new relation \(P,J,R\) have degree at most one and \(S\) is constant. If \(P,J,R\) all vanish identically, the relation forces \(S=0\). Otherwise \(m=0\), since a nonzero rational linear polynomial cannot vanish at \(\phi\). Comparing the leading affine term with its norm lower bound gives \(P=0\) and \(J+R=0\) identically. Here \(R\ne0\) and \(R(\phi)\ne0\). Thus \(s-t=O(q^{-2})\). The rational \(s=q'/q\) is reduced by the determinant identity, whereas \(B\le q^\beta<q\). They are distinct and \(|s-t|\ge1/(qB)\), giving the contradiction and proving (1).

## Consequences for the actual residual tail

Let \(Q=10^n\), let \(U=U_n\) be the reduced residual height, and let \(x_{\mathrm{rev}}=b/U\), where \(b\) is the denominator of the penultimate convergent of \(V_n/U_n\). By [prefix reconstruction](DYNAMICS.md#fixed-algebraic-centers-of-the-reversed-tail), \(|s-x_{\mathrm{rev}}|\le U^{-2}\). With the logarithmic scales from Ridout, \(q=Q^{1+o(1)}\) and \(U=Q^{1/2+o(1)}\). Thus (1) transfers to \(x_{\mathrm{rev}}\) with base \(Q\) for every \(0<\epsilon<1\) and every \(\beta<\min(\epsilon/4,1/7)\), by using a slightly smaller \(\epsilon\) and a slightly larger \(\beta\) in (1).

For every \(\epsilon>0\) we obtain the uniform weighted bound
\[
 B^{9/2}|x_{\mathrm{rev}}-A/B|>Q^{-\epsilon}
 \quad\text{eventually for all reduced } A/B\in[0,1]\text{ distinct from }x_{\mathrm{rev}}.
\tag{3}
\]
Indeed, determinant separation gives \(|x_{\mathrm{rev}}-A/B|\ge1/(UB)\). On an exceptional subsequence, the exponents \(\log B/\log Q\) therefore have a convergent subsequence with limit \(u\le (1-2\epsilon)/7<1/7\). It suffices to consider \(0<\epsilon<1/4\). Choose \(\beta>u\) with \(\beta<1/7\), and then \(\eta\) with \(4\beta<\eta<\min(1,(9/2)u+\epsilon)\), taking \(\beta\) sufficiently close to \(u\). The exceptions satisfy \(B\le Q^\beta\) and \(|x_{\mathrm{rev}}-A/B|\le Q^{-\eta}\) eventually, contradicting the transferred (1). In particular the same separation holds with \(B^7\) as weight.

For denominators \(B\le Q^{1/8}\), the same subsequence argument gives the stronger \(B^4|x_{\mathrm{rev}}-A/B|>Q^{-\epsilon}\), since \(u\le1/8<1/7\) and one can choose \(4\beta<\eta<\min(1,4u+\epsilon)\). This local bound is enough to control every quotient. For a residual quotient \(a\), write \(D_L,D_R\) for the preceding convergent denominators in the forward and reversed expansions at that quotient. The positive continued-fraction matrices give \(aD_LD_R\le U\). Indeed, in the product of the left word, the matrix with first entry \(a\), and the right word, the \((1,1)\) entry includes the product of these three first entries. The right word and its reversal have the same \((1,1)\) entry by transposition. Both expansions are canonical because the forward residual has first and last quotients at least two.

The standard error at a preceding convergent of denominator \(D\), with next quotient \(a\), is at most \(1/(aD^2)\). The [forward fourth-power bound](MOVING_CENTERS.md) gives \(a<Q^\epsilon D_L^2\) simultaneously at every position. Equation (3) gives \(a<Q^\epsilon D_R^{5/2}\), hence also \(a<Q^\epsilon D_R^5\) in the reverse direction. If \(D_R\le Q^{1/8}\), the local fourth-power reverse bound gives \(a<Q^\epsilon D_R^2\). Together with the forward bound and \(aD_LD_R\le U\), this gives \(a^2\le UQ^\epsilon\). If \(D_R>Q^{1/8}\), use just the forward estimate and the height inequality to get \(a^{3/2}\le UQ^{\epsilon/2-1/8}\). In both cases \(U=Q^{1/2+o(1)}\) yields the uniform consequence
\[
\max a\le Q^{1/4+o(1)}.
\]
Each fixed number of final quotients is subexponential by (3), applied inductively from denominator one in the reverse expansion. The growth bound still permits individual interior quotients to carry a positive fraction of the full logarithmic cost, and it gives no limit for the normalized cost of the complete deterministic orbit.

The [palindromic comparison](DYNAMICS.md#subexponential-digits-can-carry-a-positive-fraction-of-the-cost) also satisfies stronger separation in both directions and weak Gauss statistics. Its exceptional interior cost is spread across subexponential digits, so even eliminating every single exponential digit would leave the orbit mean undetermined.
