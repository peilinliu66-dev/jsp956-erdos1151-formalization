import Erdos1151.NonemptyAtomData
import Erdos1151.TentBlockExtension
import Erdos1151.NonemptyAtomBlock
import Erdos1151.ChebyshevMassAll
import Erdos1151.NonemptyTheorem

noncomputable section
open Filter Topology

namespace Erdos1151

theorem exists_layer_cutoff (κ ε : ℝ) (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ R : ℕ, 1 ≤ R ∧ 1 / (κ * ((R : ℝ) + 1)) ≤ ε := by
  have hn : Tendsto (fun R : ℕ => (R : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun R => (by linarith : (R : ℝ) ≤ (R : ℝ) + 1))
      tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun R : ℕ => (1 : ℝ) / (κ * ((R : ℝ) + 1)))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hn.const_mul_atTop hκ)
  obtain ⟨R, hR, hv⟩ := ((eventually_ge_atTop 1).and
    (ht.eventually (gt_mem_nhds hε))).exists
  exact ⟨R, hR, hv.le⟩

theorem uniform_cos_not_node (θ κ : ℝ) (hκ : 0 < κ)
    (hcos : ∀ d : ℕ, κ ≤ |Real.cos ((d : ℝ) * θ)|) :
    ∀ (d : ℕ) (k : Fin d), Real.cos θ ≠ node d k := by
  intro d k h
  have hz := eval_T_node d k
  rw [← h, Polynomial.Chebyshev.T_real_cos] at hz
  push_cast at hz
  have hb := hcos d
  rw [hz, abs_zero] at hb
  linarith

/-- The actual individual Chebyshev spikes, with every analytic and
arithmetic input now instantiated. -/
theorem exists_chebyshev_spike (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi)
    (hcos : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, δ ≤ |Real.cos ((n : ℝ) * θ)|)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n > N, ∃ ψ : C(Interval, ℝ),
      ‖ψ‖ ≤ ε ∧ chebyshevOperator (Real.cos θ) n ψ = 1 ∧
      (∀ k ≤ N, chebyshevOperator (Real.cos θ) k ψ = 0) ∧
      (∀ k, k ≠ n → |chebyshevOperator (Real.cos θ) k ψ| ≤ ε) ∧
      Tendsto (fun k => chebyshevOperator (Real.cos θ) k ψ) atTop (𝓝 0) := by
  obtain ⟨κ, hκ, hbound⟩ := hcos
  have hmass := layerMass_tendsto θ hθ ⟨κ, hκ, hbound⟩
  obtain ⟨R, hR, hRsmall⟩ := exists_layer_cutoff κ ε hκ hε
  obtain ⟨n, hn, hmpos, hv⟩ := NonemptyAssembly.exists_large_finiteAtomValue_small
    N R θ κ ε hκ hε hbound hmass
  have hn0 : 0 < n := by omega
  have hmne : ∀ s ∈ NonemptyAssembly.oddLayers R,
      NonemptyAssembly.layerMass (n * s) θ ≠ 0 := by
    intro s hs
    exact (hmpos s ((NonemptyAssembly.mem_oddLayers s R).mp hs).1).ne'
  have hcosne : ∀ d : ℕ, Real.cos ((d : ℝ) * θ) ≠ 0 :=
    fun d => abs_pos.mp (hκ.trans_le (hbound d))
  have hpoint := uniform_cos_not_node θ κ hκ hbound
  refine ⟨n, hn, continuous_spike_of_atomic
    (NonemptyAssembly.finiteAtomSupport n R) (NonemptyAssembly.finiteAtomValue n R θ)
    θ ε hθ hε (fun α _ => hv α)
    (fun α hα => NonemptyAssembly.finiteAtomSupport_cos_ne_of_uniform hκ hbound hα)
    N n hn ?_ ?_ ?_⟩
  · rw [NonemptyAssembly.atomicAngularEvaluation_finiteAtomValue]
    exact NonemptyAssembly.finiteAtomResponse_diagonal hn0 hR θ hmne hcosne hpoint
  · intro k hk
    rw [NonemptyAssembly.atomicAngularEvaluation_finiteAtomValue]
    exact NonemptyAssembly.finiteAtomResponse_before θ (hk.trans_lt hn)
  · intro k hkn
    rw [NonemptyAssembly.atomicAngularEvaluation_finiteAtomValue]
    exact (NonemptyAssembly.finiteAtomResponse_off_diagonal hn0 hkn
      θ κ hκ (hbound n) hmne hcosne hpoint).trans hRsmall

theorem exists_chebyshev_nonempty_cluster (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi)
    (hcos : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, δ ≤ |Real.cos ((n : ℝ) * θ)|)
    (A : Set ℝ) (hclosed : IsClosed A) (hsub : A ⊆ Set.Icc (-1 : ℝ) 1)
    (hne : A.Nonempty) :
    ∃ f : C(Interval, ℝ), finiteClusterSet (fun n => chebyshevOperator (Real.cos θ) n f) = A :=
  realize_nonempty_chebyshev_of_spikes (Real.cos θ)
    (exists_chebyshev_spike θ hθ hcos) A hclosed hsub hne

end Erdos1151
