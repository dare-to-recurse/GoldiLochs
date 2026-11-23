# Approximation by moving rational centers

This argument concerns the residual ratios of the specified decimal truncations. Its number-field Subspace Theorem applications are conventional arguments and remain unformalized in Lean.

## Uniform bound and its consequences

Use the notation in [PROMPT.txt](PROMPT.txt) and suppress the index \(n\). Set \(x=V/U=v/u\). For every \(\epsilon>0\), for all sufficiently large \(n\), every reduced rational \(t=p/q\in[0,1]\) with \(q\ge1\) and \(t\ne x\) satisfies
\[
q^4 |x-p/q|>Q^{-\epsilon}. \tag{1}
\]
No logarithmic scale hypothesis is required for (1).

Write the canonical continued fraction of \(x\) as \([0;b_1,\ldots,b_\tau]\), with convergents \(p_j/q_j\), \(q_0=1\), \(q_{-1}=0\), and \(q_\tau=U\). For each \(0\le j<\tau\), the determinant identity and the continued-fraction error bound give \(|x-p_j/q_j|\le 1/(q_j q_{j+1})\). Therefore (1) implies the simultaneous bounds
\[
q_{j+1}<Q^\epsilon q_j^3,\qquad
b_{j+1}<Q^\epsilon q_j^2.
\]
Also \(b_{j+1}\le U/q_j\), since \(b_{j+1}q_j\le q_{j+1}\le U\). The combination gives
\[
\max_{1\le i\le\tau} b_i < U^{2/3}Q^{\epsilon/3}.
\]
Indeed, cube the bound on one digit by using \(Q^\epsilon q_j^2\) once and \(U/q_j\) twice. At the last step one also gets \(q_{\tau-1}>U^{1/3}Q^{-\epsilon/3}\). More generally, iterating \(q_{j+1}<Q^\epsilon q_j^3\) backwards yields, for \(1\le s\le\tau\),
\[
\log q_{\tau-s}>
3^{-s}\log U-\tfrac12(1-3^{-s})\epsilon\log Q.
\]
With the scale \(\log U/\log Q\to 1/2\) from Ridout's theorem and the finite split, the largest digit is at most \(Q^{1/3+o(1)}\), and every fixed number \(s\) of final steps is preceded by a convergent of denominator at least \(Q^{1/(2\cdot 3^s)-o(1)}\). Starting from \(q_0=1\) and applying the same bound forwards gives \(\log q_j/\log Q\to0\) for fixed \(j\) and \(\tau\to\infty\) under that scale. To see that these fixed indices eventually exist, if \(\tau\le j\) infinitely often, the bound would imply \(\log U/\log Q\le (3^j-1)\epsilon/2\) on those indices, for arbitrarily small fixed \(\epsilon\).

The improvement over the determinant bound \(q^4|x-p/q|\ge q^3/U\) is confined to small enough denominators. In particular, once \(q^3\ge U\), (1) follows from the determinant alone for any such rational \(x\). The new bound rules out a large jump while the preceding denominator is too small. It still permits exponential digits after the denominator has grown and gives no estimate for the average contributions of the many intervening bounded digits.

## Proof of (1)

Let \(K=\mathbb Q(\sqrt5)\), let a prime denote conjugation, and let \(S\) be the archimedean places and the finite places above \(2\) and \(5\). Use product-formula absolute values. In particular, each real place uses the square root of the corresponding real absolute value. Put
\[
w=\phi^{-2k},\quad H_0=A+Q/\phi,\quad
z(y)=\frac{1-\phi y}{1+y/\phi}.
\]
The exact phase identity is \(\delta=wH_0z(x)\). The known bounds \(0<x\le 1/2\), \(\phi^{-4}\le z(x)<1\), \(0<\delta<1\), and \(\delta\ge(\sqrt5 Q)^{-1}\) give \(cQ^{-2}\le w\le C Q^{-1}\) with fixed positive \(c,C\). For the last bound on \(\delta\), use the nonzero integer \(A^2-AQ-Q^2=-\delta H_0\), where \(H_0=\sqrt5 Q-\delta\). These facts also give \(w\to0\) and \(A/Q\to\phi\). The function \(z\) is Lipschitz on \([0,1]\).

For \(t=p/q\), put \(\alpha=q+p/\phi\) and \(\beta=q-\phi p=\alpha'\). Use the vector \(X=(\alpha Q,\alpha A,\beta Qw,\beta Aw)\in K^4\). For variables \(Y=(Y_1,Y_2,Y_3,Y_4)\) define \(E(Y)=\phi Y_1-Y_2-\phi^{-1}Y_3-Y_4\). Then
\[
E(X)=\alpha\delta-\beta wH_0
=\alpha\delta\left(1-\frac{z(t)}{z(x)}\right),\qquad E(X)'=E(X)/w.
\]
The conjugate formula follows from \(\delta'=-H_0\), \(H_0'=-\delta\), and \(w'=1/w\). The identity
\[
z(x)-z(t)=\frac{\sqrt5(t-x)}{(1+x/\phi)(1+t/\phi)}
\]
gives \(E(X)\ne0\) when \(t\ne x\) and \(|E(X)|\le C_1 q\delta|x-t|\) in the distinguished real embedding.

At the distinguished real place take the forms \(Y_1,Y_3,E,\phi Y_3-Y_4\). Their last two values are \(E(X),\beta w\delta\). At the conjugate real place take \(Y_1,Y_3,\phi'Y_1-Y_2,E\). Their last two values after applying the embedding are \(\beta\delta,E(X)/w\). Each list is linearly independent, as seen on the coefficients of \(Y_2,Y_4\) after the two coordinate forms. At every finite place of \(S\) take the coordinate forms.

The product over \(S\) of the absolute values of the first and third coordinates is at most \(C_2q^2\). Both \(Q\) and \(Qw\) are \(S\)-units, and the finite factors of the integral elements \(\alpha,\beta\) are at most one. The product of the last two form values across the two real places, including the square-root weights, is \(|E(X)|\,|\beta|\,\delta\). The remaining two finite-place coordinate factors are at most one. Hence
\[
\prod_{\nu\in S}\prod_{i=1}^4|L_{\nu,i}(X)|_\nu
 \le C_3 q^4\delta^2 |x-t|.
\]
Outside \(S\), the local maximum of the four coordinate absolute values is one. Indeed, \(Q,w\) are local units there. If both \(\alpha,\beta\) were nonunits, the determinant \(-\sqrt5\) of the transformation from \((q,p)\) to \((\alpha,\beta)\) is a local unit and would force \(p,q\) both to be nonunits, contrary to coprimality. At the two real places the ordinary maxima are \(O(qQ)\) and \(O(qQ^3)\), respectively. The multiplicative projective height thus satisfies \(H(X)=O(qQ^2)\).

Fix \(\epsilon>0\) and suppose that (1) fails at infinitely many indices \(n\) with \(q\le Q\). The product bound is \(O(Q^{-\epsilon})\), and \(H(X)=O(Q^3)\). For some fixed \(\eta>0\) and all sufficiently large indices the product is at most \(H(X)^{-\eta}\). Since the local maxima outside \(S\) are one, the Subspace Theorem in projective form applies and places all such vectors in finitely many proper \(K\)-linear subspaces. See equation (2.11) in [Evertse and Schlickewei, The Absolute Subspace Theorem](https://pub.math.leidenuniv.nl/~evertsejh/98-absolute.pdf).

On a recurring subspace there is a fixed relation with coefficients \(a,b,c,d\in K\), not all zero:
\[
(a+bA/Q)\alpha+(c+dA/Q)\beta w=0.
\]
Divide by \(\alpha\), which is at least \(q\), and use \(|\beta|=O(q)\) and \(A/Q\to\phi\). The result is \(a+b\phi=0\). Conjugate the original relation and multiply by \(w/\alpha\) to get \(c'+d'A/Q=O(w)\), which implies \(c+d\phi'=0\). Substitute both equalities into the relation to get \(b\alpha\delta=d\beta wH_0\). Since \(\beta\ne0\) for rational \(t\), if \(b=0\) then \(d=0\), which forces all coefficients to vanish. For \(b\ne0\) the relation gives \(d/b=z(x)/z(t)\). Along the proposed exceptions, \(|x-t|\le Q^{-\epsilon}/q^4\to0\), so the uniform lower bound on \(z(x)\) and Lipschitz continuity give \(d/b=1\). This forces \(E(X)=0\), a contradiction. Thus only finitely many exceptional indices have \(q\le Q\). The others are excluded by the determinant bound \(q^4|x-p/q|\ge q^3/U\), since \(U\le Q\). Here \(U\le Q\) follows because the initial quotient is one and removing that quotient makes the first entry \(Q\), after which Euclidean entries decrease.

## Fixed algebraic centers and periodic blocks

The three-coordinate fixed-center argument in [RESEARCH.md](RESEARCH.md) works for every fixed real algebraic \(t\in[0,1]\). Enlarge \(K\) to \(F=\mathbb Q(\sqrt5,t)\), take the distinguished real place to be the given embedding, and include all archimedean places and all finite places above \(2,5\) in \(S\). Use \(Y=(Q,A,Qw)\). In addition to the first and third coordinate forms, at the distinguished place take \(\phi Y_1-Y_2-\sqrt5 z(t)Y_3\). Its value is \(O(|x-t|+w)\). At each other archimedean place, choose \(\phi Y_1-Y_2\) or \(\phi' Y_1-Y_2\) so that the coefficient is sent to the positive \(\phi\) under the local embedding. Thus the locally evaluated third form there has ordinary magnitude \(\delta<1\). At the finite places of \(S\) use coordinate forms.

For \(0<\epsilon\le1\) the assumption \(|x-t|\le Q^{-\epsilon}\) gives raw product \(O(Q^{-\epsilon/[F:\mathbb Q]})\). The coordinate contributions of \(Q,Qw\) cancel by the product formula, the finite factor of \(A\) is at most one, the local maxima outside \(S\) are one, and \(H(Y)=O(Q^3)\). The recurring subspace relation would read \(a+bA/Q+c w=0\) with coefficients in \(F\). If \(c\ne0\), any field embedding of \(F\) extending the nontrivial embedding of \(\mathbb Q(\sqrt5)\) yields an unbounded term \(\sigma(c)/w\) and bounded remaining terms. If \(c=0\), taking limits gives \(a+b\phi=0\), while substituting it back gives \(b\delta=0\). Both cases are impossible for a nontrivial relation. An exponent larger than one is covered by the result with exponent one. Thus for every fixed algebraic center \(t\in[0,1]\) and every \(\epsilon>0\), eventually \(|x-t|>Q^{-\epsilon}\).

In particular, after any fixed initial word, the start of the tail cannot repeat any fixed word for a positive linear number of digits infinitely often. Such a block and its fixed initial word determine the same cylinder as an eventually periodic infinite continued fraction. Its value is a fixed quadratic irrational. A cylinder of \(m\) digits has diameter at most the inverse square of its convergent denominator. This denominator is at least \(F_{m+1}\), so the diameter decreases exponentially in \(m\). The fixed-center bound excludes the resulting exponentially close approach when \(m\) is at least a positive constant times \(n\).

## Fixed polynomial congruences modulo the Fibonacci number

For every fixed nonzero polynomial \(P\in\mathbb Z[T]\), one has
\[
\log\gcd(F_{k_n},|P(10^n)|)=o(n). \tag{2}
\]
This follows from the all-place inequality in Proposition 4 of [Corvaja and Zannier, A Lower Bound for the Height of a Rational Function at S-unit Points](https://arxiv.org/pdf/math/0311030). In the proposition, take the number field \(K=\mathbb Q(\sqrt5)\), the places \(S\) used above, the \(S\)-units \(s=-\phi^{2k_n}\), \(t=10^n\), and the polynomials \(r_1(T)=T-1\), \(r_2(T)=P(T)\). Because \(r_1(0)=-1\), for every \(\eta>0\) the proposition bounds
\[
-\sum_{\nu}\log\min\{1,\max(|r_1(s)|_\nu,|r_2(t)|_\nu)\}
\le\eta\max\{h(s),h(t)\}
\]
outside finitely many exceptional points and finitely many translates of proper subtori. Each translate lies in an equation \(s^a t^b=c\) with \(a,b\in\mathbb Z\) not both zero. If \(b\ne0\), a valuation above \(2\) fixes \(n\), since \(s\) is an algebraic unit. If \(b=0\), the distinguished real absolute value fixes \(k_n\). The phase bounds above imply \(k_n\to\infty\) and \(k_n=O(n)\), so every translate meets the specified sequence in only finitely many indices and \(\max\{h(s),h(t)\}=O(n)\).

Since \(k_n\) is odd, Binet's formula gives \(s-1=-\sqrt5\,\phi^{k_n}F_{k_n}\). At finite places the integral factor \(\sqrt5\,\phi^{k_n}\) has absolute value at most one. Thus the finite-place part of the sum on the left bounds the log of the integer gcd from above, by the local-degree normalization of absolute values. The archimedean terms are nonnegative, and \(\eta\) was arbitrary. This proves (2).

The same phase bounds and Binet's formula give \(F_{k_n}\ge c_1\sqrt Q\) for a constant \(c_1>0\). In particular, (2) rules out \(10^{mn}\equiv\pm1\pmod{F_{k_n}}\) eventually for each fixed \(m\ge1\), and the residue formula \(v_n\equiv-F_{k_n+1}10^n\pmod{F_{k_n}}\) cannot agree infinitely often with any fixed integer multiple of \(F_{k_n+1}\). For the latter claim use \(\gcd(F_{k_n+1},F_{k_n})=1\) to cancel \(F_{k_n+1}\) and apply (2) to \(P(T)=T+c\) for the fixed multiple \(c\).

More generally, the multiplicative order of \(10^n\) modulo the largest divisor \(D_n\) of \(F_{k_n}\) coprime to \(10\) tends to infinity. Indeed, \(P(T)=T\) shows that \(\gcd(F_{k_n},10^n)=\exp(o(n))\). The valuations of \(F_{k_n}\) at \(2,5\) are therefore less than \(n\) eventually. It follows that \(F_{k_n}/D_n=\gcd(F_{k_n},10^n)\) eventually, so \(D_n\) is still exponential in \(n\). For any fixed \(M\), apply (2) to the finitely many \(P(T)=T^m-1\) with \(1\le m\le M\) to exclude every order at most \(M\) for all sufficiently large \(n\). This rules out bounded-order modular returns. Equation (2) supplies no distribution law for the particular lifted residues.

## What is still needed for an average

The scale and both avoidance conclusions admit different normalized depths. To see this, choose a transcendental real number \(\theta\in(0,1)\) with continued-fraction digits in \(\{2,3\}\), which exists by uncountability of these digit sequences and countability of the algebraic numbers. For each \(n\), form a rational by taking the first \(\lfloor\sqrt n\rfloor\) digits of \(\theta\), then appending \(m_n\) copies of \(a\), where \(a=2\) for even \(n\), \(a=3\) for odd \(n\), and
\[
m_n=\left\lfloor\frac{\log Q}{2\log \rho_a}\right\rfloor,\qquad
\rho_a=\tfrac12(a+\sqrt{a^2+4}).
\]
The continuant recurrence and the concatenation identity give \(\log U=(1/2)\log Q+O(\sqrt n)\) for these example denominators, because the homogeneous block has denominator comparable to \(\rho_a^{m_n}\) and the prefix contributes \(O(\sqrt n)\) to the log of the denominator. Their ratios converge to \(\theta>0\), so the numerators have the same logarithmic scale and every fixed algebraic center is separated by a positive distance eventually.

Every example rational also satisfies (1) eventually for each \(\epsilon>0\), uniformly in the rational center. Complete its finite continued fraction to an infinite one with all digits at most three. The completion is within \(U^{-2}\) of the rational and satisfies \(|y-p/q|\ge c_0/q^2\) for an absolute \(c_0>0\), by the bounded-partial-quotient criterion for bad approximation. For \(q\le U^{1/3}\), subtraction of \(U^{-2}\) yields \(|x-p/q|\ge c_0/(2q^2)\) for all sufficiently large \(U\). For \(q>U^{1/3}\) and \(p/q\ne x\), the determinant gives \(q^4|x-p/q|\ge q^3/U>1\).

The example depth is \(\lfloor\sqrt n\rfloor+m_n\), so the even and odd normalized depths \(\tau/\log U\) tend respectively to \(1/\log\rho_2\) and \(1/\log\rho_3\). These are distinct. Bounded-height and periodic-block avoidance therefore leave the orbit average undetermined even when all digits are bounded. For the target, the still-required step is control of the total logarithmic cost along the complete selected Euclidean trajectories. This must use more of the arithmetic of the decimal selection than the scale and approximation restrictions above.

The same two avoidance bounds also permit sublinear depth. Keep the \(\lfloor\sqrt n\rfloor\)-digit prefix of \(\theta\), then append \(\lfloor\sqrt n\rfloor\) copies of \(B_n=\lfloor\exp(\log Q/(2\lfloor\sqrt n\rfloor))\rfloor\). The continuant of the repeated block lies between \(B_n^{\lfloor\sqrt n\rfloor}\) and \((B_n+1)^{\lfloor\sqrt n\rfloor}\). The prefix adds \(O(\sqrt n)\) to its logarithmic height, so \(\log U=(1/2)\log Q+O(\sqrt n)\), while the entire length is \(O(\sqrt n)\). The ratios still converge to \(\theta\), which gives fixed algebraic center avoidance. For reduced rational centers with \(q\le U^{1/3}\), complete the finite expansion with digits at most \(B_n\). The bounded-digit approximation estimate and the \(U^{-2}\) completion error give \(|x-p/q|\ge 1/(2(B_n+2)q^2)\) eventually, since \(B_n=Q^{o(1)}\). The determinant inequality again handles \(q>U^{1/3}\). Hence (1) and the logarithmic height scale alone give no positive lower bound on \(\liminf\tau/\log U\).

Both constructions can also avoid every fixed algebraic center at the other end. After the repeated block, append the reverse of the first \(\lfloor\sqrt n\rfloor\) digits of a second transcendental number with digits in \(\{2,3\}\). Reversing the complete continued fraction starts with that second prefix and converges to the second transcendental number. The extra block adds \(O(\sqrt n)\) to both digit count and log height, and the maximum-digit estimates used for (1) still apply. Fixed-center avoidance at both ends therefore still permits different normalized depths.
