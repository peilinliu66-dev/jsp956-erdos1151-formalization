import Erdos1151.BlockSelection
import Erdos1151.InterpolationOperator
import Erdos1151.Cluster

noncomputable section
open Filter Topology

namespace Erdos1151

/-- A final assembly bridge, pending the actual one-spike construction.
The row shift deals with the harmless zero-node row without altering the
finite cluster set. -/
theorem realize_nonempty_chebyshev_of_spikes (x : ℝ)
    (hspike : ∀ (N : ℕ) (ε : ℝ), 0 < ε →
      ∃ n > N, ∃ ψ : C(Interval, ℝ),
        ‖ψ‖ ≤ ε ∧ chebyshevOperator x n ψ = 1 ∧
        (∀ k ≤ N, chebyshevOperator x k ψ = 0) ∧
        (∀ k, k ≠ n → |chebyshevOperator x k ψ| ≤ ε) ∧
        Tendsto (fun k => chebyshevOperator x k ψ) atTop (𝓝 0))
    (A : Set ℝ) (hclosed : IsClosed A) (hsub : A ⊆ Set.Icc (-1 : ℝ) 1)
    (hne : A.Nonempty) :
    ∃ f : C(Interval, ℝ), finiteClusterSet (fun n => chebyshevOperator x n f) = A := by
  let T : ℕ → C(Interval, ℝ) →L[ℝ] ℝ := fun n => chebyshevOperator x (n + 1)
  have hshift : ∀ (N : ℕ) (ε : ℝ), 0 < ε →
      ∃ n > N, ∃ ψ : C(Interval, ℝ),
        ‖ψ‖ ≤ ε ∧ T n ψ = 1 ∧
        (∀ k ≤ N, T k ψ = 0) ∧
        (∀ k, k ≠ n → |T k ψ| ≤ ε) ∧
        Tendsto (fun k => T k ψ) atTop (𝓝 0) := by
    intro N ε hε
    obtain ⟨n, hn, ψ, hnorm, hdiag, hzero, hoff, hdecay⟩ := hspike (N + 1) ε hε
    have hn1 : n - 1 + 1 = n := by omega
    refine ⟨n - 1, by omega, ψ, hnorm, ?_, ?_, ?_, ?_⟩
    · simpa only [T, hn1] using hdiag
    · intro k hk
      exact hzero (k + 1) (by omega)
    · intro k hk
      exact hoff (k + 1) (by omega)
    · exact hdecay.comp (tendsto_add_atTop_nat 1)
  obtain ⟨S⟩ := NonemptyAssembly.exists_blockFamily_of_spike T hshift
  obtain ⟨f, hf⟩ := NonemptyAssembly.realize_nonempty_of_block_family
    T S (1 : C(Interval, ℝ))
    (fun n => chebyshevOperator_one x (n + 1) (by omega)) A hclosed hsub hne
  refine ⟨f, ?_⟩
  rw [← finiteClusterSet_shift (fun n => chebyshevOperator x n f) 1]
  ext z
  exact hf z

end Erdos1151
