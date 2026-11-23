# GoldiLochs research status

**Verdict: unresolved.** The exact pointwise limit in [PROMPT.txt](PROMPT.txt) has neither a proof nor a refutation here.

## Kernel-checked unconditional results

- [Definitions](GoldiLochs/Definitions.lean) fixes $Q_n=10^n$, $A_n=\lfloor\phi Q_n\rfloor$, and $L_n=E(A_n,Q_n)$. The Euclidean recursion decreases in its second argument. The target casts $L_n$ and $n$ to reals before dividing, takes value zero at $n=0$, and uses the exact proposed constant.
- [Truncation](GoldiLochs/Truncation.lean) proves the real floor equals the integer-square-root implementation for every $n$. It proves $0<\delta_n<1$ and the recursions $A_{n+1}=10A_n+e_{n+1}$ and $\delta_{n+1}=10\delta_n-e_{n+1}$, with $0\le e_{n+1}<10$.
- [Euclid](GoldiLochs/Euclid.lean) identifies Euclidean depth with the length of mathlib's regular continued fraction including the integer part. The final convergent recovers the input and the last coefficient of a noninteger rational is at least two. Cancelling the gcd preserves depth.
- [Split](GoldiLochs/Split.lean) proves the leading run of ones has odd length $k_n$, the surviving pair has $u_n\ge 2v_n>0$ for $n\ge1$, and the reduced pair $(U_n,V_n)$ is coprime. It establishes $L_n=k_n+\tau_n$, Fibonacci reconstruction, the signed quadratic-form identity, and the action of the quotient-one step on the two real linear forms. [Phase](GoldiLochs/Phase.lean) ties the reduced ratio $V_n/U_n$ to $\delta_n$ and $k_n$.
- [Scale](GoldiLochs/Scale.lean) gives explicit uniform additive error bounds for $2\log u_n-\log Q_n-\log\delta_n$ and $k_n\log\phi+\log u_n-\log Q_n$.
- [Gauss](GoldiLochs/Gauss.lean) identifies the finite Euclidean remainder ratios with actual iterates of the Gauss map starting at $V_n/U_n$. The sum of their negative logarithms through the last positive remainder is $\log U_n$.
- [Exceptional](GoldiLochs/Exceptional.lean) proves that the original truncations' normalized length after removing the integer part is eventually above $12\log(2)/\pi^2$ by a fixed positive margin.
- [Arithmetic](GoldiLochs/Arithmetic.lean) proves that the reduced denominator $q_n$ divides $Q_n$ and satisfies $3q_n^2>Q_n$, so $q_n\to\infty$. Fibonacci reconstruction and Cassini's identity give $F_{k_n}A_n=v_n+F_{k_n+1}Q_n$. The phase bounds imply $0<v_n<6F_{k_n}$, so $v_n$ is among at most six lifts of one residue class.
- [Potential](GoldiLochs/Potential.lean) proves that the nonnegative logarithmic cost of a Euclidean step vanishes at quotient one. The sum of this cost over the reduced tail, plus $\log d_n$, is exactly $\log(\sqrt 5\,Q_n-\delta_n)-L_n\log\phi$. The fixed target is equivalent, without Diophantine hypotheses, to that total cost divided by $n$ tending to $\log 10-C\log\phi$.
- [Backward](GoldiLochs/Backward.lean) verifies the determinant and exact error of the penultimate convergent of $V_n/U_n$. It bounds the cube of the final quotient times the fourth-power-weighted error by $U_n^2$. [Phase](GoldiLochs/Phase.lean) reduces the moving-center linear form exactly to $\sqrt5\,\phi^{-k_n}(p u_n-q v_n)$.
- [Continuants](GoldiLochs/Continuants.lean) identifies each digit of the actual residual list with mathlib's canonical continued-fraction stream after the integer part. For every digit $a$ with preceding continuant denominators $D_L$ and $D_R$ from the two ends, it proves $aD_LD_R\le U_n$ and gives reduced, distinct approximants with errors at most $1/(aD_L^2)$ and $1/(aD_R^2)$.
- [Potential](GoldiLochs/Potential.lean) compares the golden cost and the logarithmic digit mass above a cutoff within a factor of two. Lean proves that, for the actual selected tails, making either normalized contribution eventually arbitrarily small is equivalent to making the other small.

## Kernel-checked conditional results

Under the two explicit hypotheses $-\log\delta_n/n\to0$ and $\log d_n/n\to0$, Lean proves
$k_n/n\to\log(10)/(2\log\phi)$ and
$\log U_n/n\to\log(10)/2$.
Under those hypotheses, the [collection theorem](GoldiLochs/Basic.lean) makes the fixed target equivalent to the negative log mean along the actual finite Gauss orbits tending to $\pi^2/(12\log 2)$. [Tail](GoldiLochs/Tail.lean) proves this mean law is equivalent to $\tau_n/\log U_n\to12\log 2/\pi^2$.

Lean also proves both logarithmic hypotheses from the explicit lower bound on the reduced-fraction error $\delta_n/Q_n\ge q_n^{-1-\epsilon}$, assumed eventually for each $\epsilon>0$. This isolates the remaining Ridout instance in the collection theorem.

[Quotient bounds](GoldiLochs/QuotientBounds.lean) proves that every residual quotient is at most $Q_n^{1/4+\epsilon}$ eventually for every $\epsilon>0$. It takes the residual-height limit and two separation bounds as explicit hypotheses. The forward fourth-power separation is global, and the reverse fourth-power separation applies to center denominators at most $Q_n^{1/8}$. The two separation bounds use conventional Subspace Theorem arguments.

## Published inputs and scope

Bugeaud's Theorem 6.6 gives only finitely many exceptional pairs of nonzero integers `(p,q)`, with `q > 0`, for which `min(1, |φ − p/q|)` times the product of the `ℓ`-adic factors `|pq|_ℓ` for `ℓ ∈ {2,5}` is less than `q^(−2−ε)`. For the reduced truncation `p = A_n/d_n`, `q = Q_n/d_n`, the factors from `q` multiply to `1/q` and those from `p` multiply to at most one. The reduced denominators tend to infinity because bounded denominators would leave finitely many candidates in `[1,2]`, whereas the truncations converge to the irrational `φ`. Thus for every `ε > 0`, eventually `δ_n ≥ d_n^(1+ε) Q_n^(−ε)`. Taking logarithms gives `0 ≤ −log δ_n + (1+ε) log d_n ≤ ε n log 10`, which implies both required scale limits. Searches of the pinned mathlib sources and Lean LSP surfaced Dirichlet, Hurwitz, Liouville, and continued-fraction approximation results. The required Ridout instance remains unformalized. [Bugeaud, *Expansions of algebraic numbers*, Theorem 6.6](https://irma.math.unistra.fr/~bugeaud/travaux/FFNT.pdf)

**Fixed-denominator statistics.** David, Kim, Mor and Shapira bound the proportion of reduced numerators with a fixed normalized length deviation at denominator `q` by a negative power of `q`. Their subset version still samples uniformly from a large set. For the selected reduced numerator `V_n` at denominator `U_n`, the needed proposition is eventual avoidance of the exceptional set for every fixed deviation threshold. The counting bound leaves the selected numerator's membership undetermined. The original truncations are themselves eventually exceptional for a small fixed threshold, as Lean verifies in Exceptional.lean. The estimate for the prefix alone forces this deviation. [David, Kim, Mor and Shapira, Theorems 1.2–1.3](https://arxiv.org/html/2401.15586v2)

**Finite-orbit statistics.** Aka and Shapira control averages over the entire continued-fraction period of `10^n φ`, whose length grows on the scale `10^n`. A segment with `O(n)` terms contributes only `O(n/10^n)` to bounded full-period averages. A proof via Gauss dynamics must control the trajectory from the specific rational `V_n/U_n` over its finite Euclidean lifetime. For weak convergence to imply the mean of `−log x`, it must also bound the contribution from ratios near zero uniformly. Faivre's Lochs-type result counts the common prefix certified by the two decimal endpoints. [Aka and Shapira, Theorem 2.8 and Corollary 2.13](https://arxiv.org/pdf/1201.1280) [Faivre, *On calculating a continued fraction expansion from a decimal expansion*](https://www.acta.hu/download.phtml?id=2622)

## Deterministic tail research

[Moving centers](MOVING_CENTERS.md) strengthens the earlier [six-coordinate argument](RESEARCH.md). The four-coordinate Subspace Theorem proof gives $q^4|V_n/U_n-p/q|>Q_n^{-\epsilon}$ eventually for each $\epsilon>0$, simultaneously for every distinct reduced rational center in $[0,1]$. Consequently every proper convergent satisfies $q_{j+1}<Q_n^\epsilon q_j^3$. Under Ridout's height scale the largest quotient is at most $Q_n^{1/3+o(1)}$. The argument also excludes initial repetitions of any fixed periodic word for a positive linear number of digits. A separate $S$-unit argument in the same note excludes bounded multiplicative order of $Q_n$ modulo the part of $F_{k_n}$ coprime to $10$. These Diophantine applications remain conventional proofs.

The comparison family in [Moving centers](MOVING_CENTERS.md) satisfies the strengthened height and approximation bounds and has two different subsequential normalized depths. The exact missing lemma for the GoldiLochs pairs is that for each $\epsilon>0$, eventually every $n$ satisfies
```math
\left|\frac{\tau_n}{\log U_n}-\frac{12\log 2}{\pi^2}\right|<\epsilon.
```
[Dynamics](DYNAMICS.md) gives an equivalent bounded-observable problem on each exact geodesic segment. The conventional reverse-center argument also excludes exponential proximity to each fixed algebraic center after reversal. With the height scale, the actual last quotient is therefore subexponential and fixed periodic terminal blocks have sublinear length. A comparison family with weak Gauss convergence and both endpoint exclusions has normalized depth tending to half the candidate rate, due to one large interior quotient. A discrete Gauss-map proof needs control over the contribution from small ratios reached inside the trajectory.

[Reverse moving centers](REVERSE_MOVING.md) strengthens the reverse estimate to moving rational centers. The proof gives the local fourth-power bound used by Lean's quarter-exponent estimate, and makes every fixed final quotient subexponential under the height scale. The [palindromic comparison](DYNAMICS.md#subexponential-digits-can-carry-a-positive-fraction-of-the-cost) meets stronger bounds in both directions and has weak Gauss statistics with a subexponential maximum digit. A sparse group of middle digits still changes its normalized depth. Even with weak Gauss convergence, a proof for the selected tails needs a uniform estimate on the sum of logarithms above a growing cutoff.

The six-lift description gives an arithmetic formulation. To use it for the limit requires information about the Euclidean trajectories after choosing the lift of $-F_{k_n+1}10^n\bmod F_{k_n}$ selected by the decimal truncation. The congruence and lift bound leave open how often that trajectory has an atypical normalized length.

A refutation by isolated large quotients would require an infinite subsequence and a proved net effect on the normalized depth. The fixed-index argument excludes an exponential quotient there. At the last quotient, an exceptionally small penultimate denominator $q'$ would give $p q'\equiv\pm1\bmod q$, where $p/q$ is the reduced truncation. This implies $\gcd(q',q)=1$ and supplies no $\{2,5\}$-smooth denominator for another application of Ridout. The congruence alone has yielded neither an infinite exceptional subsequence nor an aggregate error bound.

## Exact integer diagnostics

| Decimal places | Prefix | Tail | Total |
| ---: | ---: | ---: | ---: |
| 1 | 3 | 1 | 4 |
| 10 | 25 | 9 | 34 |
| 100 | 239 | 93 | 332 |
| 1,000 | 2,395 | 951 | 3,346 |

These values were recomputed using integer square root and Euclidean division.

## Reproducing the checkpoint

Lean is pinned to `v4.37.0-rc1` and mathlib to `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. [lake-manifest.json](lake-manifest.json) records the transitive package pins.

```sh
lake build
lake env lean scripts/audit.lean
lake env leanchecker --verbose GoldiLochs
```

The build passed without Lean compiler diagnostics. The standalone audit checks an independently spelled version of the fixed proposition, prints its fully elaborated definition and the complete conditional theorem type, and reports transitive dependencies for the results above. Their dependencies are contained in `propext`, `Classical.choice`, and `Quot.sound`. The bundled `leanchecker` replayed the project modules using Lean's kernel.

Nanoda 0.4.31 type-checked separate exports of the earlier reduction and of this checkpoint's `target_iff_decimalGoldenCost`, `movingCenter_error_identity`, and `residualLastEuclideanQuotient_weighted_error_le` with the same three axioms permitted. It reported no type-checking errors and one separate pretty-printing error for axioms on each export. The locally installed `lean4lean` binary rejected the object-file format as incompatible.
