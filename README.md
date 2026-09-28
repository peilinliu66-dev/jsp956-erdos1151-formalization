# JSP-000956 / Erdős 1151

Lean formalization of prescribed finite cluster sets for Chebyshev–Lagrange interpolation.

## Status

Complete for the JSP-000956 / Erdős 1151 historical specified-point statement, including the empty target set. The complete project and both final statements passed local Lean checking on 2026-09-28.

The main endpoints are `Erdos1151.erdos_1151` and `Erdos1151.erdos_1151_polynomial` in `Erdos1151/Main.lean`. For every natural numerator `p`, odd natural denominator `q`, and closed set `A` contained in `[-1,1]`, they construct a continuous function whose interpolation sequence at `cos(p*pi/q)` has finite real cluster set exactly `A`.

The genuine whole-sequence strong-divergence theorem is also proved:

`Erdos1151.rational_chebyshev_strong_divergence_all`

For natural numbers `p,q` with `Odd q`, there is a continuous real function on `[-1,1]` such that the absolute values of its actual Chebyshev interpolation values at `cos(p*pi/q)` tend to infinity. These results have no unproved sieve, node-geometry, mass-growth, block-spike or convergence assumptions.

The nonempty-set construction uses actual primitive-node layers, Möbius cancellation and continuous finite-tent extensions. Every hypothesis of the final block-family assembly is instantiated. See `PROOF_GUIDE.md` and `STATEMENT_CORRESPONDENCE.md`.

## Mathematical meaning

`interpolationPolynomial n f` is mathlib's Lagrange interpolation polynomial at the `n` Chebyshev roots. `interpolationPolynomial_degree` proves degree `< n`, `interpolationPolynomial_node` proves the prescribed nodal values, and `interpolationPolynomial_eval` identifies its evaluation with `chebyshevOperator`.

`finiteClusterSet` is the set of real `MapClusterPt` values of the full sequence. It does not include points at infinity. The zero-node row has no effect on this set, as proved by `finiteClusterSet_shift`.

## Reproduction

Lean: `leanprover/lean4:v4.33.0`.

Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`, pinned in both the package configuration and manifest.

From this directory, with the stated Lean toolchain installed:

```sh
lake exe cache get
lake build
lake env lean Check.lean
```

Both full prescribed-cluster-set endpoints and the strong-divergence endpoint were checked to depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Mathematical sources and contribution

- P. Erdős, *On Divergence Properties of the Lagrange Interpolation Parabolas*, Annals of Mathematics 42 (1941), 309–315: https://www.renyi.hu/~p_erdos/1941-02.pdf
- P. Erdős, *Corrections to Two of My Papers*, Annals of Mathematics 44 (1943), 647–651: https://www.renyi.hu/~p_erdos/1943-03.pdf
- *Chebyshev–Lagrange limit sets and the variants of an Erdős problem*, 2026 research note: https://www.ulam.ai/research/erdos1151.pdf
- Problem source: https://www.erdosproblems.com/1151

This is a formalization of known mathematical arguments, with an independently implemented elementary primitive-node count and sparse-tent convergence route. It is not a claim of a new mathematical solution. The 1943 correction is essential: the verified assertion is absolute-value divergence along the whole sequence.

The project Lean code was independently developed from these mathematical sources and mathlib. Formalization contribution: `peilinliu66-dev`, with Codex AI assistance. This local verification is a compiler check; award review is performed by the organizers.
