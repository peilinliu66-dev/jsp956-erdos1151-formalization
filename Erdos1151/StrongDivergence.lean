import Erdos1151.Triangular
import Erdos1151.Sparse
import Erdos1151.Cluster

/-!
The complete functional-analytic assembly of the corrected construction.
The remaining problem-specific task is to supply actual Chebyshev bumps and
prove their primitive diagonal mass grows at the required rate.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace Erdos1151

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem exists_strong_divergence_of_sparse_bumps
    (L : ℕ → C(X, ℝ) →L[ℝ] ℝ) (b : ℕ → C(X, ℝ)) (w : ℕ → ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : ∀ n, 0 ≤ w n)
    (hwm : Antitone w) (hwlim : Tendsto w atTop (𝓝 0))
    (hb : ∀ n x, |b n x| ≤ 1)
    (hdec : ∀ n m, n < m → ∀ x, b n x ≠ 0 → b m x ≠ 0 →
      w m ≤ q * w n)
    (htri : ∀ n m, n < m → L n (b m) = 0)
    (hdiag : ∀ n, 0 ≤ L n (b n))
    (hgrowth : Tendsto (fun n => w n * L n (b n)) atTop atTop) :
    ∃ f : C(X, ℝ), Tendsto (fun n => |L n f|) atTop atTop := by
  let v : ℕ → C(X, ℝ) := fun n => w n • b n
  let σ : ℕ → ℝ := recursiveSign L v
  have hσ : ∀ n, |σ n| ≤ 1 := by
    intro n
    rcases recursiveSign_cases L v n with h | h <;> simp [σ, h]
  obtain ⟨f, hf⟩ := sparse_continuousMap_weighted_limit b w σ
    hq0 hq1 hw0 hwm hwlim hσ hb hdec
  have hconv : Tendsto (signedPartial L v) atTop (𝓝 f) := by
    change Tendsto (fun N => signedPartial L v N) atTop (𝓝 f)
    simpa only [signedPartial_eq_sum, v, σ] using hf
  refine ⟨f, strong_divergence_of_triangular_limit L v ?_ ?_ f hconv ?_⟩
  · intro n m hnm
    simp [v, htri n m hnm]
  · intro n
    simpa [v] using mul_nonneg (hw0 n) (hdiag n)
  · simpa [v] using hgrowth

theorem exists_empty_clusterSet_of_sparse_bumps
    (L : ℕ → C(X, ℝ) →L[ℝ] ℝ) (b : ℕ → C(X, ℝ)) (w : ℕ → ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : ∀ n, 0 ≤ w n)
    (hwm : Antitone w) (hwlim : Tendsto w atTop (𝓝 0))
    (hb : ∀ n x, |b n x| ≤ 1)
    (hdec : ∀ n m, n < m → ∀ x, b n x ≠ 0 → b m x ≠ 0 →
      w m ≤ q * w n)
    (htri : ∀ n m, n < m → L n (b m) = 0)
    (hdiag : ∀ n, 0 ≤ L n (b n))
    (hgrowth : Tendsto (fun n => w n * L n (b n)) atTop atTop) :
    ∃ f : C(X, ℝ), finiteClusterSet (fun n => L n f) = ∅ := by
  obtain ⟨f, hf⟩ := exists_strong_divergence_of_sparse_bumps L b w
    hq0 hq1 hw0 hwm hwlim hb hdec htri hdiag hgrowth
  exact ⟨f, finiteClusterSet_eq_empty_of_abs_tendsto_atTop hf⟩

end Erdos1151
