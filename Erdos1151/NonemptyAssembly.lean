import Mathlib
import Erdos1151.NonemptySequence

/-!
Independent Banach-space block-spike assembly from Section 5 of the public
paper `Chebyshev–Lagrange limit sets and the variants of an Erdős problem`.
No Chebyshev block spike is asserted here: the explicit hypotheses below
must be supplied by the analytic construction.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace Erdos1151.NonemptyAssembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def spikePartial (T : ℕ → E →L[ℝ] ℝ) (ψ : ℕ → E)
    (rows : ℕ → ℕ) (a : ℕ → ℝ) (c : ℝ) : ℕ → E
  | 0 => 0
  | m + 1 => spikePartial T ψ rows a c m +
      (a m - c - T (rows m) (spikePartial T ψ rows a c m)) • ψ m

def coefficient (T : ℕ → E →L[ℝ] ℝ) (ψ : ℕ → E)
    (rows : ℕ → ℕ) (a : ℕ → ℝ) (c : ℝ) (m : ℕ) : ℝ :=
  a m - c - T (rows m) (spikePartial T ψ rows a c m)

theorem spikePartial_eq_sum (T : ℕ → E →L[ℝ] ℝ) (ψ : ℕ → E)
    (rows : ℕ → ℕ) (a : ℕ → ℝ) (c : ℝ) (m : ℕ) :
    spikePartial T ψ rows a c m =
      ∑ i ∈ Finset.range m, coefficient T ψ rows a c i • ψ i := by
  induction m with
  | zero => simp [spikePartial]
  | succ m ih => rw [Finset.sum_range_succ, spikePartial, ← ih]; rfl

/-- The summably small interactions keep the recursively corrected
interpolation coefficients uniformly bounded. -/
theorem coefficient_bound (T : ℕ → E →L[ℝ] ℝ) (ψ : ℕ → E)
    (rows : ℕ → ℕ) (a ε : ℕ → ℝ) (c B : ℝ)
    (hrows : StrictMono rows) (hB : 0 ≤ B)
    (ha : ∀ m, |a m - c| ≤ B)
    (hε : ∀ i, 0 ≤ ε i) (hεsum : Summable ε) (hεsmall : ∑' i, ε i ≤ 1 / 2)
    (hoff : ∀ i n, n ≠ rows i → |T n (ψ i)| ≤ ε i) :
    ∀ m, |coefficient T ψ rows a c m| ≤ 2 * B := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hsum : |T (rows m) (spikePartial T ψ rows a c m)| ≤ B := by
      rw [spikePartial_eq_sum, map_sum]
      calc
        |∑ i ∈ Finset.range m, T (rows m) (coefficient T ψ rows a c i • ψ i)|
            ≤ ∑ i ∈ Finset.range m,
                |T (rows m) (coefficient T ψ rows a c i • ψ i)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range m, 2 * B * ε i := by
          apply Finset.sum_le_sum
          intro i hi
          have him : i < m := Finset.mem_range.mp hi
          rw [map_smul, smul_eq_mul, abs_mul]
          exact mul_le_mul (ih i him)
            (hoff i (rows m) (ne_of_gt (hrows him))) (abs_nonneg _) (by positivity)
        _ = 2 * B * ∑ i ∈ Finset.range m, ε i := by rw [Finset.mul_sum]
        _ ≤ 2 * B * (∑' i, ε i) :=
          mul_le_mul_of_nonneg_left
            (hεsum.sum_le_tsum _ (fun i _ => hε i)) (by positivity)
        _ ≤ 2 * B * (1 / 2) := mul_le_mul_of_nonneg_left hεsmall (by positivity)
        _ = B := by ring
    exact (abs_sub _ _).trans (by linarith [ha m])

variable [CompleteSpace E]

theorem summable_corrected_spikes (T : ℕ → E →L[ℝ] ℝ) (ψ : ℕ → E)
    (rows : ℕ → ℕ) (a : ℕ → ℝ) (c B : ℝ)
    (hb : ∀ m, |coefficient T ψ rows a c m| ≤ 2 * B)
    (hψ : Summable (fun m => ‖ψ m‖)) :
    Summable (fun m => coefficient T ψ rows a c m • ψ m) := by
  apply (hψ.mul_left (2 * B)).of_norm_bounded
  intro m
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb m) (norm_nonneg _)

/-- Exact values on selected rows; all future spikes vanish at those rows. -/
theorem selected_value (T : ℕ → E →L[ℝ] ℝ) (ψ : ℕ → E)
    (rows : ℕ → ℕ) (a : ℕ → ℝ) (c : ℝ) (z : E)
    (hz : ∀ n, T n z = c)
    (hdiag : ∀ m, T (rows m) (ψ m) = 1)
    (hfuture : ∀ m i, m < i → T (rows m) (ψ i) = 0)
    (hsum : Summable (fun i => coefficient T ψ rows a c i • ψ i)) (m : ℕ) :
    T (rows m) (z + ∑' i, coefficient T ψ rows a c i • ψ i) = a m := by
  rw [map_add, hz, (T (rows m)).map_tsum hsum]
  rw [tsum_eq_sum (s := Finset.range (m + 1)) (fun i hi => by
    have hmi : m < i := by simpa using hi
    simp [map_smul, hfuture m i hmi])]
  rw [Finset.sum_range_succ]
  have hprefix : (∑ i ∈ Finset.range m, T (rows m)
      (coefficient T ψ rows a c i • ψ i)) = T (rows m) (spikePartial T ψ rows a c m) := by
    rw [spikePartial_eq_sum, map_sum]
  rw [hprefix, map_smul, hdiag, smul_eq_mul, mul_one, coefficient]
  ring

/-- On non-selected rows, the sum tends to the baseline. This is the
nontrivial exclusion of spurious finite cluster points. -/
theorem complement_value_tendsto (T : ℕ → E →L[ℝ] ℝ) (ψ : ℕ → E)
    (rows : ℕ → ℕ) (a ε : ℕ → ℝ) (c B : ℝ) (z : E)
    (hz : ∀ n, T n z = c)
    (hb : ∀ m, |coefficient T ψ rows a c m| ≤ 2 * B)
    (hB : 0 ≤ B) (hεsum : Summable ε)
    (hoff : ∀ i n, n ≠ rows i → |T n (ψ i)| ≤ ε i)
    (hdecay : ∀ i, Tendsto (fun n => T n (ψ i)) atTop (𝓝 0))
    (hsum : Summable (fun i => coefficient T ψ rows a c i • ψ i)) :
    Tendsto (fun n => T n (z + ∑' i, coefficient T ψ rows a c i • ψ i))
      (atTop ⊓ 𝓟 (Set.range rows)ᶜ) (𝓝 c) := by
  have hdom := tendsto_tsum_of_dominated_convergence
    (f := fun n i => coefficient T ψ rows a c i * T n (ψ i))
    (g := fun _ => (0 : ℝ)) (𝓕 := atTop ⊓ 𝓟 (Set.range rows)ᶜ)
    (hεsum.mul_left (2 * B))
    (fun i => by simpa using
      (tendsto_const_nhds.mul (hdecay i)).mono_left inf_le_left)
    (show ∀ᶠ n in atTop ⊓ 𝓟 (Set.range rows)ᶜ,
      ∀ i, ‖coefficient T ψ rows a c i * T n (ψ i)‖ ≤ 2 * B * ε i from by
      apply Filter.eventually_inf_principal.mpr
      filter_upwards [] with n hn i
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hb i) (hoff i n (fun h => hn ⟨i, h.symm⟩))
        (abs_nonneg _) (by positivity))
  have hlim : Tendsto
      (fun n => c + ∑' i, coefficient T ψ rows a c i * T n (ψ i))
      (atTop ⊓ 𝓟 (Set.range rows)ᶜ) (𝓝 c) := by
    simpa using tendsto_const_nhds.add hdom
  convert hlim using 1
  ext n
  rw [map_add, hz, (T n).map_tsum hsum]
  congr 1
  apply tsum_congr
  intro i
  simp only [map_smul, smul_eq_mul]

/-- Explicit analytic input needed for the nonempty construction.

In the paper, the finite zero block and uniform post-block bound imply
`off_diagonal`; separation of the selected blocks implies `future_zero`;
off-point decay implies `decay`; choosing row sizes gives `norm_summable`.
This structure does not assert that Chebyshev interpolation supplies it.
-/
structure BlockFamily (T : ℕ → E →L[ℝ] ℝ) where
  rows : ℕ → ℕ
  spike : ℕ → E
  error : ℕ → ℝ
  rows_strictMono : StrictMono rows
  diagonal : ∀ i, T (rows i) (spike i) = 1
  future_zero : ∀ m i, m < i → T (rows m) (spike i) = 0
  error_nonneg : ∀ i, 0 ≤ error i
  error_summable : Summable error
  error_small : ∑' i, error i ≤ 1 / 2
  off_diagonal : ∀ i n, n ≠ rows i → |T n (spike i)| ≤ error i
  norm_summable : Summable (fun i => ‖spike i‖)
  decay : ∀ i, Tendsto (fun n => T n (spike i)) atTop (𝓝 0)

/-- A genuine block-spike family realizes every nonempty closed target
inside [-1,1]. The conclusion has no restriction on the chosen target. -/
theorem realize_nonempty_of_block_family
    (T : ℕ → E →L[ℝ] ℝ) (S : BlockFamily T)
    (one : E) (hone : ∀ n, T n one = 1)
    (A : Set ℝ) (hclosed : IsClosed A) (hsub : A ⊆ Set.Icc (-1 : ℝ) 1)
    (hne : A.Nonempty) :
    ∃ f : E, ∀ x, MapClusterPt x atTop (fun n => T n f) ↔ x ∈ A := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨a, hain, ha⟩ := exists_sequence_clusterSet A hclosed ⟨c, hc⟩
  have hac : ∀ m, |a m - c| ≤ 2 := by
    intro m
    have ham := hsub (hain m)
    have hcm := hsub hc
    rw [abs_le]
    constructor <;> linarith [ham.1, ham.2, hcm.1, hcm.2]
  have hb := coefficient_bound T S.spike S.rows a S.error c 2 S.rows_strictMono
    (by norm_num) hac S.error_nonneg S.error_summable S.error_small S.off_diagonal
  have hsum := summable_corrected_spikes T S.spike S.rows a c 2 hb S.norm_summable
  let f : E := c • one + ∑' i, coefficient T S.spike S.rows a c i • S.spike i
  have hz : ∀ n, T n (c • one) = c := by intro n; simp [hone n]
  refine ⟨f, clusterSet_of_selected_and_complement S.rows_strictMono hclosed hc ha hain ?_ ?_⟩
  · intro m
    exact selected_value T S.spike S.rows a c (c • one) hz S.diagonal S.future_zero hsum m
  · exact complement_value_tendsto T S.spike S.rows a S.error c 2 (c • one) hz hb
      (by norm_num) S.error_summable S.off_diagonal S.decay hsum

end Erdos1151.NonemptyAssembly

