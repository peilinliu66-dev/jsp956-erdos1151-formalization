# Proof guide: JSP-000956 / Erdős 1151

## Statement and mathematical sources

For natural numbers $p,q$ with $q$ odd, put $x_0=\cos(p\pi/q)$.
For every closed $A\subseteq[-1,1]$, including $A=\varnothing$, the formalization constructs

$$
f\in C([-1,1],\mathbb R),\qquad
\operatorname{Cl}_{\mathbb R}\{L_nf(x_0):n\to\infty\}=A.
$$

Here $L_nf$ is the actual degree-$<n$ Lagrange interpolation polynomial at the $n$ roots of $T_n$. The cluster set consists of finite real subsequential limits. The function $f$ is continuous; its range is not required to lie in $[-1,1]$.

The final theorems are `Erdos1151.erdos_1151` and `Erdos1151.erdos_1151_polynomial` in `Erdos1151/Main.lean`. The polynomial degree, nodal values, and equality with the finite evaluation operator are proved in `InterpolationOperator.lean`. Removing or shifting finitely many initial rows preserves the cluster set.

The mathematical sources are:

1. P. Erdős, [*On divergence properties of the Lagrange interpolation parabolas*](https://www.renyi.hu/~p_erdos/1941-02.pdf), Annals of Mathematics 42 (1941), 309–315.
2. P. Erdős, [*Corrections to two of my papers*](https://www.renyi.hu/~p_erdos/1943-03.pdf), Annals of Mathematics 44 (1943), 647–651, especially the correction beginning on p. 647. The recursive row-sign choice below implements the corrected whole-sequence absolute-divergence argument.
3. The ULAM research note [*Chebyshev–Lagrange limit sets and the variants of an Erdős problem*](https://www.ulam.ai/research/erdos1151.pdf), 29 April 2026, especially Sections 2, 4, and 5, for the finite-layer construction and nonempty-cluster-set assembly.

This is a formalization of known mathematical arguments. The proofs below use explicit elementary sieve estimates, quantitative sparse tents, and a direct continuous-extension estimate.

## 1. Actual nodes, coefficients, and primitive rows

Write

$$
\phi_{n,k}=\frac{(2k+1)\pi}{2n},\quad x_{n,k}=\cos\phi_{n,k},\quad
\ell_{n,k}(x)=(\text{Lagrange basis at }x_{n,k})(x).
$$

The factorization of $T_n$, together with its derivative at its simple roots, gives

$$
\ell_{n,k}(\cos\theta)=
\frac{\cos(n\theta)\sin\phi_{n,k}}
 {n(\cos\theta-\cos\phi_{n,k})(-1)^k}.
$$

The theorem `coefficient_formula` proves this identity for mathlib's `Lagrange.basis`. The absolute-value identity is `abs_coefficient_formula`.

A node is primitive in row $n$ when $(2k+1,n)=1$. Equality of two nodes is equivalent to

$$
(2k+1)m=(2j+1)n.
$$

Consequently, a primitive row-$n$ node cannot occur in a smaller row. Distinct nodes from rows at most $N$ satisfy $|x-y|\ge N^{-3}$: their angles differ by at least $\pi/(2nm)$, and the cosine-difference identity combined with the linear sine lower bound gives $1/(Nnm)$.
These facts are `node_eq_iff_cross_mul`, `primitive_ne_earlier`, and `node_separation`.

After reducing and reflecting the angle, assume $0\le\theta\le\pi$. Odd $q$ implies $\cos(np\pi/q)\ne0$ for every $n$, since a zero would equate an even integer with an odd integer. Periodicity modulo $2q$ therefore supplies a constant $\kappa>0$ with

$$
|\cos(n\theta)|\ge\kappa\quad\text{for every }n.
$$

See `rational_cos_uniform_lower` and `rational_cos_normalized`.

## 2. Primitive coefficient mass grows on every sufficiently large row

Let $P(n)$ be the distinct odd prime divisors of $n$, $w=|P(n)|$, and set

$$
\rho(n)=\prod_{p\in P(n)}(1-1/p),\qquad E(n)=2^w,\qquad
S_n=\sum_{(2k+1,n)=1}|\ell_{n,k}(x_0)|.
$$

For every integer interval $[a,a+M)$, finite inclusion–exclusion proves

$$
\left|\#\{k\in[a,a+M):(2k+1,n)=1\}-M\rho(n)\right|\le E(n).
$$

Each squarefree product of odd primes imposes one residue class, whose interval count differs from $M/d$ by at most one (`primitive_count_error`). No prime number theorem or Mertens estimate is used.

The ordered odd primes satisfy $p_i\ge2i+1$. Squaring the product and telescoping yields

$$
\rho(n)^2(2w+1)\ge1,\qquad 3^w\le n,\qquad E(n)^3\le n^2.
$$

Thus, for $n\ge3$, $\rho(n)\sqrt{\log n}\ge c_0=\sqrt{\log3/3}>0$, and eventually

$$
2E(n)\le\rho(n)n^{3/4}.
$$

The last step follows from $\sqrt{\log n}/n^{1/12}\to0$, and is proved as `primitive_error_eventually_absorbed`.

For an interior angle, let $k_n=\lfloor n\theta/\pi+1/2\rfloor$ and use indices $k_n+m-1$, where $1\le m\le cn$ and $c=(\pi-\theta)/(2\pi)>0$. Their angles lie between $\theta$ and $\theta+\pi m/n$; their sines have a fixed lower bound $s>0$. Therefore

$$
|\ell_{n,k_n+m-1}(x_0)|\ge\frac{\kappa s}{\pi m}.
$$

The sieve is uniform under this index translation. Every dyadic shell starting beyond $\lceil n^{3/4}\rceil$ contributes at least $\rho(n)/4$ to the primitive reciprocal sum. Between that cutoff and $\lfloor cn\rfloor$ there are eventually at least $\log n/(8\log2)$ such shells. Hence $S_n\ge C\rho(n)\log n\ge C'\sqrt{\log n}$.
At $x_0=1$, indices $k=m-1$, $1\le m\le n/4$, instead satisfy $|\ell_{n,m-1}(1)|\ge4/(\pi^2m)$; reflection handles $-1$.
The resulting all-angle statement is `exists_primitiveMass_lower` in `ChebyshevMassAll.lean`.

## 3. Empty target: continuous tents and whole-sequence divergence

At each primitive row-$n$ node put a triangular tent of radius $r_n=1/(4n^6)$, with sign chosen to agree with its coefficient at $x_0$. Let the sum be $b_n$. Node separation proves

$$
\|b_n\|_\infty\le1,\qquad L_nb_n(x_0)=S_n,\qquad
L_nb_m(x_0)=0\quad(m>n).
$$

If $b_n(x)$ and $b_m(x)$ are both nonzero with $n<m$, the same separation estimate forces $m>n^2$. Put $a_n=(\log n)^{-1/4}$ for $n\ge2$. Along the active rows at any fixed point, these weights decrease by at least the factor $2^{-1/4}<1$. Uniformly in $x$, every signed tail is consequently bounded by

$$
\sum_{n\ge N}a_n|b_n(x)|\le\frac{(\log N)^{-1/4}}{1-2^{-1/4}}.
$$

This proves uniform convergence and continuity for every choice of row signs. Choose the sign of $a_nb_n$ recursively to agree with the current interpolation value of the preceding partial sum, choosing $+1$ at zero. The new row then has absolute value at least $a_nS_n$; all future rows vanish at its nodes. The uniform limit $f$ therefore satisfies

$$
|L_nf(x_0)|\ge a_nS_n\ge C'(\log n)^{1/4}\longrightarrow\infty.
$$

The sign recursion is `diagonal_lower_bound` and `strong_divergence_of_triangular_limit`; sparse convergence and actual tents are discharged before `rational_chebyshev_strong_divergence_all`. This gives the empty finite cluster set along the entire sequence.

## 4. Nonempty target: finite Möbius layers produce an isolated row

Normalize the signed primitive table in row $d$ by $S_d$, obtaining an angular atom $a_d$ with its own row response one and pointwise magnitude at most $1/S_d$ (`primitiveAtom_diagonal`, `primitiveAtom_abs_le`). A primitive row-$d$ node occurs in row $j$ exactly when $j=dv$ with $v$ odd. Its coefficient transfer factor is

$$
\frac1v\chi(v)\frac{\cos(dv\theta)}{\cos(d\theta)},\qquad
\chi(v)=(-1)^{(v-1)/2}.
$$

Primitive order is unique, so these are exact responses of the finite tables (`primitive_coefficient_transfer`, `NonemptyAtomResponse.lean`). For a base row $n$ and cutoff $R\ge1$, combine the odd layers $ns$, $s\le R$, with amplitudes

$$
A_s=\frac{\mu(s)\chi(s)\cos(ns\theta)}{s\cos(n\theta)}.
$$

The response vanishes unless the row is $nu$ with $u$ odd. In that case it equals

$$
\frac{\chi(u)\cos(nu\theta)}{u\cos(n\theta)}
\sum_{s\mid u,\ s\le R}\mu(s).
$$

Möbius inversion makes this one at $u=1$ and zero for $1<u\le R$. For every $u\ne1$, the truncated sum is the negative of the omitted divisor sum. The injection $s\mapsto u/s$ bounds the number of divisors $s>R$ by $u/(R+1)$, giving the uniform off-row bound $1/(\kappa(R+1))$.
These are `finite_layer_delta`, `uniform_tail_layer_bound`, and `finiteAtomResponse_off_diagonal`.

First choose $R$ to make this bound at most $\varepsilon$. Then take $n$ sufficiently large that all $S_{ns}\ge M$, $s\ge1$, with $R/(\kappa M)\le\varepsilon$. This is possible because the actual masses tend to infinity on all rows. The combined table has amplitude at most $\varepsilon$, response one at $n$, zero before $n$, and response at most $\varepsilon$ on every other row.

## 5. Continuous extension preserves all required row estimates

The table has finite angular support $P\subset(0,\pi)$, avoiding the evaluation point in cosine distance. Replace each table value by a narrow angular tent and compose the resulting function with $\arccos$. Choose a large finite row cutoff $K$, then choose the radius so that the table is preserved exactly at every node through row $K$, and the tents have disjoint supports.

If $|v|\le V$, the cosine-distance margin is $d>0$, and the radius is $r\le d/2$, direct counting of the angular grid gives

$$
|L_n\psi(x_0)|\le\frac{2V|P|}{d}\left(\frac{2r}{\pi}+\frac1n\right).
$$

Choosing $K$ large and then $r$ small controls every later row. The norm remains at most $V$. For the fixed resulting function, convergence $L_n\psi(x_0)\to0$ is proved separately: its angular version $\varphi$ vanishes near $\theta$, so

$$
H(t)=\frac{\varphi(t)\sin t}{\cos\theta-\cos t}
$$

extends continuously across $\theta$. Pairing adjacent terms and uniform continuity show $n^{-1}\sum_k(-1)^kH(\phi_{n,k})\to0$; the coefficient formula supplies the remaining bounded factor $\cos(n\theta)$.
Thus `continuous_spike_of_atomic` and `exists_chebyshev_spike` give genuine continuous spikes with small norm, exact selected response, exact initial zeros, uniformly small off-row responses, and decay on all sufficiently large rows.

## 6. Bounded recursive correction realizes every nonempty closed target

Choose $c\in A$ and a sequence $a_i\in A$ whose finite cluster set is exactly $A$. Apply the spike construction successively with increasing selected rows $n_i$ and errors $\varepsilon_i=4^{-(i+1)}$, so $\sum_i\varepsilon_i=1/3<1/2$. Write the spikes as $\psi_i$. Define

$$
b_i=a_i-c-L_{n_i}\left(\sum_{j<i}b_j\psi_j\right)(x_0).
$$

Since $|a_i-c|\le2$, induction using the summable off-row errors gives $|b_i|\le4$. Hence $f=c+\sum_i b_i\psi_i$ converges uniformly. Every future spike vanishes on each earlier selected row, so $L_{n_i}f(x_0)=a_i$ exactly. On the complementary rows, each fixed spike response tends to zero and is bounded by $\varepsilon_i$; summable domination therefore gives $L_nf(x_0)\to c$ along that complement. The full finite cluster set is precisely $A$.

These steps are `coefficient_bound`, `selected_value`, `complement_value_tendsto`, and `realize_nonempty_of_block_family`. `NonemptyConstruction.lean` supplies the actual Chebyshev spikes. Finally `Main.lean` splits according to whether $A$ is empty and proves the stated operator and polynomial forms.
