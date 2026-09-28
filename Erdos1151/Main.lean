import Erdos1151.NonemptyConstruction
import Erdos1151.StrongDivergenceTheorem

/-!
The full historical prescribed-cluster-set theorem at rational-cosine points
with odd denominator. The target set may be empty. The polynomial statement
uses the actual degree-<n Lagrange interpolation polynomial, not an abstract
sequence of linear functionals with unproved assumptions.
-/

noncomputable section
open Filter Topology

namespace Erdos1151

theorem erdos_1151 (p q : ℕ) (hq : Odd q)
    (A : Set ℝ) (hclosed : IsClosed A) (hsub : A ⊆ Set.Icc (-1 : ℝ) 1) :
    ∃ f : C(Interval, ℝ),
      finiteClusterSet (fun n => chebyshevOperator (Real.cos (p * Real.pi / q)) n f) = A := by
  by_cases hA : A.Nonempty
  · obtain ⟨θ, hθ, hx, hcos⟩ := rational_cos_normalized p q hq
    simpa only [hx] using exists_chebyshev_nonempty_cluster θ hθ hcos A hclosed hsub hA
  · obtain ⟨f, hf⟩ := rational_chebyshev_strong_divergence_all p q hq
    exact ⟨f, (finiteClusterSet_eq_empty_of_abs_tendsto_atTop hf).trans
      (Set.not_nonempty_iff_eq_empty.mp hA).symm⟩

theorem erdos_1151_polynomial (p q : ℕ) (hq : Odd q)
    (A : Set ℝ) (hclosed : IsClosed A) (hsub : A ⊆ Set.Icc (-1 : ℝ) 1) :
    ∃ f : C(Interval, ℝ),
      finiteClusterSet (fun n => (interpolationPolynomial n f).eval
        (Real.cos (p * Real.pi / q))) = A := by
  simpa only [interpolationPolynomial_eval] using erdos_1151 p q hq A hclosed hsub

end Erdos1151
