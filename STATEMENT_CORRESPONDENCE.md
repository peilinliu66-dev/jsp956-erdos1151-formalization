# Statement correspondence

Problem: [Erdős 1151](https://www.erdosproblems.com/1151), catalog [JSP-000956](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000956).

The historical specified-point version asks for each prescribed point of the form `cos(pi*p/q)`, with positive odd integers `p,q`, and each closed set `A` contained in `[-1,1]`, a continuous function whose Chebyshev interpolation values at that point have precisely `A` as their finite real cluster set. The function may depend on both the point and the target set.

The submitted theorem `Erdos1151.erdos_1151_polynomial` has the following type:

```lean
theorem erdos_1151_polynomial (p q : ℕ) (hq : Odd q)
    (A : Set ℝ) (hclosed : IsClosed A)
    (hsub : A ⊆ Set.Icc (-1 : ℝ) 1) :
    ∃ f : C(Interval, ℝ),
      finiteClusterSet (fun n => (interpolationPolynomial n f).eval
        (Real.cos (p * Real.pi / q))) = A
```

| Original object or requirement | Formal representation |
| --- | --- |
| Continuous real function on `[-1,1]` | `C(Interval, ℝ)`, where `Interval = Set.Icc (-1) 1` |
| Chebyshev nodes | `node n k = cos((2*k+1)*pi/(2*n))`, `k : Fin n` |
| Interpolating polynomial of degree at most `n-1` | `interpolationPolynomial n f`, defined using `Lagrange.interpolate`; its degree is `< n` |
| Correct nodal values | `interpolationPolynomial_node` |
| Actual polynomial evaluation | `interpolationPolynomial_eval` identifies it with `chebyshevOperator` |
| All finite subsequential limits, and no others | `finiteClusterSet`, defined by `MapClusterPt x atTop` |
| Empty target allowed | The endpoint has no `A.Nonempty` assumption; `Main.lean` treats both cases |
| Every permitted point and target | `p`, `q`, `A` precede the existential function |
| Full sequence of positive row sizes | All natural rows are used; the initial zero-node row is immaterial by `finiteClusterSet_shift` |

The statement is slightly stronger in its numerator: no oddness or coprimality assumption on `p` is needed. `Odd q` already implies `q > 0`. An arccosine normalization handles all angle representatives, including endpoint values.

The scope is the prescribed finite-real target sets contained in `[-1,1]`. Infinite cluster values and arbitrary unbounded target sets are not part of this endpoint.

Mathematical statement evidence is given by the problem source and the fixed-point formulation of Theorem 1.1 in the 2026 research note linked in `README.md`. The proof of the strong-divergence branch follows Erdős's 1941 paper with its necessary 1943 correction. `PROOF_GUIDE.md` supplies the full construction used by the Lean implementation.

The final Lean statement is submitted for maintainer review; it is not represented as a previously maintainer-approved statement.
