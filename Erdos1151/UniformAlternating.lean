import Erdos1151.ChebyshevWeights

/-! Off-point decay via cancellation of neighboring Chebyshev grid points. -/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace Erdos1151

theorem alternating_sum_bound (g : ℕ → ℝ) (n : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 ≤ ε) (hg : ∀ k < n, |g k| ≤ B)
    (hd : ∀ k, k + 1 < n → |g k - g (k + 1)| ≤ ε) :
    |∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * g k| ≤ (n : ℝ) * ε + B := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using hB
  | one =>
    simpa using (hg 0 (by omega)).trans (by linarith : B ≤ (1 : ℝ) * ε + B)
  | more n ih _ =>
    have hn := ih (fun k hk => hg k (by omega)) (fun k hk => hd k (by omega))
    have hlast := hd n (by omega)
    have heq : (-1 : ℝ) ^ n * g n + (-1 : ℝ) ^ (n + 1) * g (n + 1) =
        (-1 : ℝ) ^ n * (g n - g (n + 1)) := by rw [pow_succ]; ring
    rw [Finset.sum_range_succ, Finset.sum_range_succ, add_assoc, heq]
    have habs := abs_add_le (∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * g k)
      ((-1 : ℝ) ^ n * (g n - g (n + 1)))
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at habs
    push_cast
    linarith

/-- Cancellation on the actual midpoint angular grids needs only continuity,
not a differentiability or bounded-variation assumption. -/
theorem chebyshev_alternating_average_tendsto (H : ℝ → ℝ)
    (hH : ContinuousOn H (Set.Icc 0 Real.pi)) :
    Tendsto (fun n : ℕ => (∑ k : Fin n, (-1 : ℝ) ^ k.val * H (angle n k)) / (n : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) Real.pi)).bddAbove_image hH.abs
  have hbound : ∀ x ∈ Set.Icc 0 Real.pi, |H x| ≤ B := fun x hx => hB ⟨x, hx, rfl⟩
  have hB0 : 0 ≤ B := (abs_nonneg (H 0)).trans (hbound 0 ⟨le_rfl, Real.pi_pos.le⟩)
  have hu := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) Real.pi)).uniformContinuousOn_of_continuous hH
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) (by positivity)
  have hpi : Tendsto (fun n : ℕ => Real.pi / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun n : ℕ => B / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hpi.eventually (gt_mem_nhds hδ))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hb.eventually (gt_mem_nhds (by positivity : 0 < ε / 2)))
  refine ⟨max (max N₁ N₂) 1, ?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsmallπ := hN₁ n (by omega)
  have hsmallB := hN₂ n (by omega)
  let g : ℕ → ℝ := fun k => H (((2 * (k : ℝ) + 1) * Real.pi) / (2 * n))
  have hgnode (k : Fin n) : g k.val = H (angle n k) := rfl
  have hg : ∀ k < n, |g k| ≤ B := by
    intro k hk
    exact hbound (angle n ⟨k, hk⟩) (angle_mem_Icc n ⟨k, hk⟩)
  have hpair : ∀ k, k + 1 < n → |g k - g (k + 1)| ≤ ε / 2 := by
    intro k hk
    let a : Fin n := ⟨k, by omega⟩
    let b : Fin n := ⟨k + 1, hk⟩
    have hstep : angle n b - angle n a = Real.pi / n := by
      simp only [angle, a, b]
      push_cast
      field_simp
      <;> ring
    have hdist : dist (angle n a) (angle n b) = Real.pi / n := by
      rw [Real.dist_eq, abs_sub_comm, hstep, abs_of_pos (by positivity)]
    have h := hclose (angle n a) (angle_mem_Icc n a)
      (angle n b) (angle_mem_Icc n b) (by simpa [hdist] using hsmallπ)
    exact h.le
  have hsum := alternating_sum_bound g n B (ε / 2) hB0 (by positivity) hg hpair
  have heq : (∑ k : Fin n, (-1 : ℝ) ^ k.val * H (angle n k)) =
      ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * g k := by
    exact Fin.sum_univ_eq_sum_range (fun k => (-1 : ℝ) ^ k * g k) n
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hnR, heq]
  apply lt_of_le_of_lt (div_le_div_of_nonneg_right hsum hnR.le)
  have heq' : ((n : ℝ) * (ε / 2) + B) / n = ε / 2 + B / n := by field_simp
  rw [heq']
  linarith

def offPointKernel (θ : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  φ x * Real.sin x / (Real.cos θ - Real.cos x)

theorem continuousOn_offPointKernel (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi)
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc 0 Real.pi))
    {ρ : ℝ} (hρ : 0 < ρ) (hzero : ∀ x, |x - θ| < ρ → φ x = 0) :
    ContinuousOn (offPointKernel θ φ) (Set.Icc 0 Real.pi) := by
  intro x hx
  by_cases heq : x = θ
  · subst x
    have hevent : ∀ᶠ y in 𝓝 θ, offPointKernel θ φ y = 0 := by
      filter_upwards [Metric.ball_mem_nhds θ hρ] with y hy
      have hy' : |y - θ| < ρ := hy
      simp [offPointKernel, hzero y hy']
    exact (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ))
      (Set.Icc 0 Real.pi) θ).congr_of_eventuallyEq
      (hevent.filter_mono nhdsWithin_le_nhds) (by simp [offPointKernel])
  · have hcos : Real.cos θ - Real.cos x ≠ 0 := by
      intro hz
      have h := Real.strictAntiOn_cos.injOn hθ hx (sub_eq_zero.mp hz)
      exact heq h.symm
    exact ((hφ x hx).mul Real.continuous_sin.continuousAt.continuousWithinAt).div
      (continuous_const.sub Real.continuous_cos).continuousAt.continuousWithinAt hcos

theorem angular_evaluation_formula (θ : ℝ) (φ : ℝ → ℝ) (n : ℕ)
    (hne : ∀ k : Fin n, Real.cos θ ≠ node n k) :
    (∑ k : Fin n, coefficient n k (Real.cos θ) * φ (angle n k)) =
      Real.cos ((n : ℝ) * θ) *
        ((∑ k : Fin n, (-1 : ℝ) ^ k.val * offPointKernel θ φ (angle n k)) / n) := by
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coefficient_formula n k θ (hne k)]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt k.isLt
  have hd : Real.cos θ - Real.cos (angle n k) ≠ 0 := sub_ne_zero.mpr (hne k)
  have hs : (-1 : ℝ) ^ k.val ≠ 0 := by positivity
  have hsquare : (-1 : ℝ) ^ k.val * (-1 : ℝ) ^ k.val = 1 := by rw [← mul_pow]; norm_num
  have hsquare' : ((-1 : ℝ) ^ k.val) ^ 2 = 1 := by simpa [pow_two] using hsquare
  unfold offPointKernel node
  field_simp
  rw [hsquare', mul_one]

/-- Every continuous function vanishing near the fixed evaluation point has
interpolation values tending to zero along the entire sequence of rows. -/
theorem chebyshev_offPoint_decay (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi)
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc 0 Real.pi))
    {ρ : ℝ} (hρ : 0 < ρ) (hzero : ∀ x, |x - θ| < ρ → φ x = 0) :
    Tendsto (fun n : ℕ => ∑ k : Fin n,
      coefficient n k (Real.cos θ) * φ (angle n k)) atTop (𝓝 0) := by
  have hkernel := continuousOn_offPointKernel θ hθ φ hφ hρ hzero
  have hlim := chebyshev_alternating_average_tendsto (offPointKernel θ φ) hkernel
  have hnormlim := hlim.norm
  simp only [norm_zero] at hnormlim
  apply squeeze_zero_norm (fun n => ?_) hnormlim
  by_cases hn : ∃ k : Fin n, Real.cos θ = node n k
  · obtain ⟨j, hj⟩ := hn
    have hjθ : angle n j = θ := Real.strictAntiOn_cos.injOn (angle_mem_Icc n j) hθ hj.symm
    have hz : φ (angle n j) = 0 := by rw [hjθ]; exact hzero θ (by simpa using hρ)
    have hsum : (∑ k : Fin n, coefficient n k (Real.cos θ) * φ (angle n k)) = 0 := by
      rw [hj]
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hkj : k = j
      · subst k
        simp [hz]
      · rw [coefficient_other n k j hkj, zero_mul]
    rw [hsum, norm_zero]
    exact norm_nonneg _
  · push Not at hn
    rw [angular_evaluation_formula θ φ n hn, norm_mul, Real.norm_eq_abs (Real.cos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)

end Erdos1151
