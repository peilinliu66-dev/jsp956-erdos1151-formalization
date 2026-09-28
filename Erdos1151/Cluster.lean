import Mathlib

noncomputable section
open Filter Topology

namespace Erdos1151

/-- Finite real cluster values of a sequence; no point at infinity is included. -/
def finiteClusterSet (u : ℕ → ℝ) : Set ℝ :=
  {x | MapClusterPt x atTop u}

theorem finiteClusterSet_shift (u : ℕ → ℝ) (k : ℕ) :
    finiteClusterSet (fun n => u (n + k)) = finiteClusterSet u := by
  unfold finiteClusterSet MapClusterPt
  change {x | ClusterPt x (Filter.map (u ∘ fun n => n + k) atTop)} = _
  rw [← Filter.map_map, Filter.map_add_atTop_eq_nat]

theorem finiteClusterSet_eq_empty_of_abs_tendsto_atTop {u : ℕ → ℝ}
    (hu : Tendsto (fun n => |u n|) atTop atTop) : finiteClusterSet u = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hnear : ∃ᶠ n in atTop, u n ∈ Metric.ball x 1 :=
    mapClusterPt_iff_frequently.mp hx _ (Metric.ball_mem_nhds x (by norm_num))
  have hlarge : ∀ᶠ n in atTop, |x| + 1 ≤ |u n| :=
    hu.eventually (eventually_ge_atTop (|x| + 1))
  obtain ⟨n, hn, hN⟩ := (hnear.and_eventually hlarge).exists
  have hn' : |u n - x| < 1 := by simpa [Real.dist_eq] using hn
  have htri : |u n| ≤ |u n - x| + |x| := by
    simpa using abs_add_le (u n - x) x
  linarith

/-- Assembly lemma: the nonempty construction and genuine strong divergence
cover every closed target set. These two premises must be proved separately. -/
theorem cluster_realization_of_nonempty_and_strong_divergence
    {F : Type*} (T : F → ℕ → ℝ)
    (hne : ∀ A : Set ℝ, IsClosed A → A ⊆ Set.Icc (-1 : ℝ) 1 → A.Nonempty →
      ∃ f : F, finiteClusterSet (T f) = A)
    (hdiv : ∃ f : F, Tendsto (fun n => |T f n|) atTop atTop) :
    ∀ A : Set ℝ, IsClosed A → A ⊆ Set.Icc (-1 : ℝ) 1 →
      ∃ f : F, finiteClusterSet (T f) = A := by
  intro A hclosed hsub
  by_cases hA : A.Nonempty
  · exact hne A hclosed hsub hA
  · obtain ⟨f, hf⟩ := hdiv
    exact ⟨f, (finiteClusterSet_eq_empty_of_abs_tendsto_atTop hf).trans
      (Set.not_nonempty_iff_eq_empty.mp hA).symm⟩

end Erdos1151
