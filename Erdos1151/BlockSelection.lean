import Erdos1151.NonemptyAssembly

/-! Selection of a summable family from individually available block spikes.
The analytic existence assumption remains explicit; this file only performs
the recursive choice and proves all assembly estimates. -/

noncomputable section
open Filter Topology

namespace Erdos1151.NonemptyAssembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def selectionError (i : ℕ) : ℝ := (1 / 4 : ℝ) ^ (i + 1)

theorem selectionError_pos (i : ℕ) : 0 < selectionError i := by
  unfold selectionError
  positivity

theorem selectionError_hasSum : HasSum selectionError (1 / 3 : ℝ) := by
  have h := (hasSum_geometric_of_abs_lt_one
    (by norm_num : |(1 / 4 : ℝ)| < 1)).mul_left (1 / 4 : ℝ)
  norm_num at h
  change HasSum (fun i : ℕ => (1 / 4 : ℝ) ^ (i + 1)) (1 / 3 : ℝ)
  simpa only [pow_succ'] using h

private structure SpikeSpec (T : ℕ → E →L[ℝ] ℝ) (N : ℕ) (ε : ℝ)
    (q : ℕ × E) : Prop where
  row_gt : N < q.1
  norm_le : ‖q.2‖ ≤ ε
  diagonal : T q.1 q.2 = 1
  initial_zero : ∀ k ≤ N, T k q.2 = 0
  off_diagonal : ∀ k, k ≠ q.1 → |T k q.2| ≤ ε
  decay : Tendsto (fun k => T k q.2) atTop (𝓝 0)

private def selectedPair (p : ℕ → ℕ → ℕ × E) : ℕ → ℕ × E
  | 0 => p 0 0
  | i + 1 => p (selectedPair p i).1 (i + 1)

private def selectedThreshold (p : ℕ → ℕ → ℕ × E) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (selectedPair p i).1

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem selectedPair_eq (p : ℕ → ℕ → ℕ × E) (i : ℕ) :
    selectedPair p i = p (selectedThreshold p i) i := by
  cases i <;> rfl

/-- Individual spikes with arbitrarily small norm and off-row interactions
give the complete input required by `realize_nonempty_of_block_family`. -/
theorem exists_blockFamily_of_spike
    (T : ℕ → E →L[ℝ] ℝ)
    (hspike : ∀ (N : ℕ) (ε : ℝ), 0 < ε →
      ∃ n > N, ∃ ψ : E,
        ‖ψ‖ ≤ ε ∧ T n ψ = 1 ∧
        (∀ k ≤ N, T k ψ = 0) ∧
        (∀ k, k ≠ n → |T k ψ| ≤ ε) ∧
        Tendsto (fun k => T k ψ) atTop (𝓝 0)) :
    Nonempty (BlockFamily T) := by
  classical
  have hex (N i : ℕ) : ∃ q : ℕ × E, SpikeSpec T N (selectionError i) q := by
    obtain ⟨n, hn, ψ, hnorm, hdiag, hzero, hoff, hdecay⟩ :=
      hspike N (selectionError i) (selectionError_pos i)
    exact ⟨(n, ψ), hn, hnorm, hdiag, hzero, hoff, hdecay⟩
  let pick (N i : ℕ) : ℕ × E := Classical.choose (hex N i)
  have hp (N i : ℕ) : SpikeSpec T N (selectionError i) (pick N i) :=
    Classical.choose_spec (hex N i)
  have hs (i : ℕ) : SpikeSpec T (selectedThreshold pick i)
      (selectionError i) (selectedPair pick i) := by
    rw [selectedPair_eq]
    exact hp _ _
  have hmono : StrictMono (fun i => (selectedPair pick i).1) := by
    apply strictMono_nat_of_lt_succ
    intro i
    exact (hs (i + 1)).row_gt
  refine ⟨{
    rows := fun i => (selectedPair pick i).1
    spike := fun i => (selectedPair pick i).2
    error := selectionError
    rows_strictMono := hmono
    diagonal := fun i => (hs i).diagonal
    future_zero := ?_
    error_nonneg := fun i => (selectionError_pos i).le
    error_summable := selectionError_hasSum.summable
    error_small := ?_
    off_diagonal := fun i => (hs i).off_diagonal
    norm_summable := ?_
    decay := fun i => (hs i).decay
  }⟩
  · intro m i hmi
    cases i with
    | zero => omega
    | succ i =>
      exact (hs (i + 1)).initial_zero _ (hmono.monotone (by omega))
  · rw [selectionError_hasSum.tsum_eq]
    norm_num
  · exact selectionError_hasSum.summable.of_nonneg_of_le
      (fun i => norm_nonneg _) (fun i => (hs i).norm_le)

end Erdos1151.NonemptyAssembly
