import Mathlib

open Filter Finset
open scoped Topology BigOperators

namespace Erdos1151

/-- A finite ordered family whose successive possible nonzero weights shrink geometrically
has a geometric sum bound. The hypothesis is deliberately on all ordered pairs: this lets
one apply the result to the support at a point without enumerating that support. -/
theorem sparse_weight_sum_le (s : Finset ℕ) (w : ℕ → ℝ) {q B : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hB : 0 ≤ B)
    (hw0 : ∀ n ∈ s, 0 ≤ w n) (hwB : ∀ n ∈ s, w n ≤ B)
    (hdec : ∀ n ∈ s, ∀ m ∈ s, n < m → w m ≤ q * w n) :
    ∑ n ∈ s, w n ≤ B / (1 - q) := by
  induction s using Finset.induction_on_min generalizing B with
  | empty => simpa using div_nonneg hB (by linarith : 0 ≤ 1 - q)
  | insert a s hmin ih =>
    have ha : a ∉ s := by
      intro ha
      exact (lt_irrefl a) (hmin a ha)
    have hwa : 0 ≤ w a := hw0 a (mem_insert_self a s)
    have hwaB : w a ≤ B := hwB a (mem_insert_self a s)
    have hs : ∑ n ∈ s, w n ≤ (q * w a) / (1 - q) := by
      apply ih (mul_nonneg hq0 hwa)
      · intro n hn
        exact hw0 n (mem_insert_of_mem hn)
      · intro n hn
        exact hdec a (mem_insert_self a s) n (mem_insert_of_mem hn) (hmin n hn)
      · intro n hn m hm hnm
        exact hdec n (mem_insert_of_mem hn) m (mem_insert_of_mem hm) hnm
    rw [sum_insert ha]
    have hd : 0 < 1 - q := by linarith
    apply (le_div_iff₀ hd).2
    have hs' := (le_div_iff₀ hd).1 hs
    nlinarith

/-- Uniform bound for a finite sum of terms whose nonzero supports overlap only at
geometrically decreasing weights. -/
theorem sparse_sum_abs_le {X : Type*} (s : Finset ℕ) (g : ℕ → X → ℝ)
    (w : ℕ → ℝ) {q B : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hB : 0 ≤ B)
    (hw0 : ∀ n ∈ s, 0 ≤ w n) (hwB : ∀ n ∈ s, w n ≤ B)
    (hg : ∀ n ∈ s, ∀ x, |g n x| ≤ w n)
    (hdec : ∀ n ∈ s, ∀ m ∈ s, n < m →
      ∀ x, g n x ≠ 0 → g m x ≠ 0 → w m ≤ q * w n) (x : X) :
    |∑ n ∈ s, g n x| ≤ B / (1 - q) := by
  classical
  let t := s.filter fun n => g n x ≠ 0
  have heq : ∑ n ∈ s, g n x = ∑ n ∈ t, g n x := by
    symm
    apply sum_subset (filter_subset _ _)
    intro n hn hnt
    simpa [t, hn] using hnt
  rw [heq]
  calc
    |∑ n ∈ t, g n x| ≤ ∑ n ∈ t, |g n x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ t, w n := sum_le_sum fun n hn => hg n (mem_filter.mp hn).1 x
    _ ≤ B / (1 - q) := by
      apply sparse_weight_sum_le t w hq0 hq1 hB
      · exact fun n hn => hw0 n (mem_filter.mp hn).1
      · exact fun n hn => hwB n (mem_filter.mp hn).1
      · intro n hn m hm hnm
        exact hdec n (mem_filter.mp hn).1 m (mem_filter.mp hm).1 hnm x
          (mem_filter.mp hn).2 (mem_filter.mp hm).2

/-- The analytic input needed by the interpolation construction: geometric sparsity
of supports gives uniform convergence even when the scalar weight series diverges. -/
theorem sparse_uniformCauchy {X : Type*} (g : ℕ → X → ℝ) (w : ℕ → ℝ)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : ∀ n, 0 ≤ w n)
    (hwm : Antitone w) (hwlim : Tendsto w atTop (𝓝 0))
    (hg : ∀ n x, |g n x| ≤ w n)
    (hdec : ∀ n m, n < m → ∀ x, g n x ≠ 0 → g m x ≠ 0 →
      w m ≤ q * w n) :
    UniformCauchySeqOn (fun N x => ∑ n ∈ range N, g n x) atTop Set.univ := by
  have hd : 0 < 1 - q := by linarith
  have htail (N n m : ℕ) (hn : N ≤ n) (hnm : n ≤ m) (x : X) :
      |(∑ i ∈ range m, g i x) - ∑ i ∈ range n, g i x| ≤ w N / (1 - q) := by
    rw [← sum_Ico_eq_sub _ hnm]
    apply sparse_sum_abs_le (Ico n m) g w hq0 hq1 (hw0 N)
    · exact fun i _ => hw0 i
    · intro i hi
      exact hwm (hn.trans (mem_Ico.mp hi).1)
    · exact fun i _ x => hg i x
    · exact fun i _ j _ hij x hi hj => hdec i j hij x hi hj
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  have hsmall : ∀ᶠ N in atTop, w N < ε * (1 - q) :=
    hwlim.eventually (gt_mem_nhds (mul_pos hε hd))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨N, ?_⟩
  intro m hm n hn x _
  have hbound : w N / (1 - q) < ε := (div_lt_iff₀ hd).2 (hN N le_rfl)
  rcases le_total n m with hnm | hmn
  · exact (htail N n m hn hnm x).trans_lt hbound
  · rw [dist_comm]
    exact (htail N m n hm hmn x).trans_lt hbound

theorem sparse_exists_uniform_limit {X : Type*} [TopologicalSpace X]
    (g : ℕ → X → ℝ) (w : ℕ → ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : ∀ n, 0 ≤ w n)
    (hwm : Antitone w) (hwlim : Tendsto w atTop (𝓝 0))
    (hg : ∀ n x, |g n x| ≤ w n)
    (hdec : ∀ n m, n < m → ∀ x, g n x ≠ 0 → g m x ≠ 0 →
      w m ≤ q * w n) (hcont : ∀ n, Continuous (g n)) :
    ∃ f : X → ℝ, Continuous f ∧
      TendstoUniformly (fun N x => ∑ n ∈ range N, g n x) f atTop := by
  have hc := sparse_uniformCauchy g w hq0 hq1 hw0 hwm hwlim hg hdec
  have hex : ∀ x : X, ∃ a : ℝ,
      Tendsto (fun N => ∑ n ∈ range N, g n x) atTop (𝓝 a) := by
    intro x
    exact cauchySeq_tendsto_of_complete (hc.cauchySeq (Set.mem_univ x))
  choose f hf using hex
  have hu : TendstoUniformly (fun N x => ∑ n ∈ range N, g n x) f atTop :=
    tendstoUniformlyOn_univ.mp (hc.tendstoUniformlyOn_of_tendsto fun x _ => hf x)
  refine ⟨f, hu.continuous ?_, hu⟩
  exact Filter.Frequently.of_forall fun N => continuous_finsetSum _ fun n _ => hcont n

/-- Signs may be chosen after the bump family is built; their choices do not affect
the convergence argument. In fact any coefficients in `[-1,1]` are allowed. -/
theorem sparse_signed_exists_uniform_limit {X : Type*} [TopologicalSpace X]
    (b : ℕ → X → ℝ) (w σ : ℕ → ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : ∀ n, 0 ≤ w n)
    (hwm : Antitone w) (hwlim : Tendsto w atTop (𝓝 0))
    (hσ : ∀ n, |σ n| ≤ 1) (hb : ∀ n x, |b n x| ≤ 1)
    (hdec : ∀ n m, n < m → ∀ x, b n x ≠ 0 → b m x ≠ 0 →
      w m ≤ q * w n) (hcont : ∀ n, Continuous (b n)) :
    ∃ f : X → ℝ, Continuous f ∧
      TendstoUniformly (fun N x => ∑ n ∈ range N, σ n * w n * b n x) f atTop := by
  apply sparse_exists_uniform_limit (fun n x => σ n * w n * b n x) w hq0 hq1 hw0 hwm hwlim
  · intro n x
    rw [abs_mul, abs_mul, abs_of_nonneg (hw0 n)]
    calc
      |σ n| * w n * |b n x| ≤ 1 * w n * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hσ n) (hw0 n)) (hb n x)
          (abs_nonneg _) (by simpa using hw0 n)
      _ = w n := by ring
  · intro n m hnm x hn hm
    apply hdec n m hnm x
    · intro h
      exact hn (by simp [h])
    · intro h
      exact hm (by simp [h])
  · intro n
    exact continuous_const.mul (hcont n)

/-- Explicit quantitative remainder bound for any uniform limit furnished above. -/
theorem sparse_uniform_limit_remainder {X : Type*}
    (g : ℕ → X → ℝ) (w : ℕ → ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : ∀ n, 0 ≤ w n)
    (hwm : Antitone w) (hg : ∀ n x, |g n x| ≤ w n)
    (hdec : ∀ n m, n < m → ∀ x, g n x ≠ 0 → g m x ≠ 0 →
      w m ≤ q * w n) {f : X → ℝ}
    (hu : TendstoUniformly (fun N x => ∑ n ∈ range N, g n x) f atTop)
    (N : ℕ) (x : X) :
    |f x - ∑ n ∈ range N, g n x| ≤ w N / (1 - q) := by
  apply le_of_tendsto ((hu.tendsto_at x).sub_const _).abs
  filter_upwards [eventually_ge_atTop N] with m hm
  rw [← sum_Ico_eq_sub _ hm]
  apply sparse_sum_abs_le (Ico N m) g w hq0 hq1 (hw0 N)
  · exact fun i _ => hw0 i
  · exact fun i hi => hwm (mem_Ico.mp hi).1
  · exact fun i _ x => hg i x
  · exact fun i _ j _ hij x hi hj => hdec i j hij x hi hj

/-- The same convergence conclusion in the normed space of continuous maps on a
compact domain. This is the interface used by continuous linear evaluation maps. -/
theorem sparse_continuousMap_limit {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : ℕ → C(X, ℝ)) (w : ℕ → ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : ∀ n, 0 ≤ w n)
    (hwm : Antitone w) (hwlim : Tendsto w atTop (𝓝 0))
    (hg : ∀ n x, |g n x| ≤ w n)
    (hdec : ∀ n m, n < m → ∀ x, g n x ≠ 0 → g m x ≠ 0 →
      w m ≤ q * w n) :
    ∃ f : C(X, ℝ), Tendsto (fun N => ∑ n ∈ range N, g n) atTop (𝓝 f) := by
  obtain ⟨f, hcont, hu⟩ := sparse_exists_uniform_limit (fun n => g n) w
    hq0 hq1 hw0 hwm hwlim hg hdec (fun n => (g n).continuous)
  refine ⟨⟨f, hcont⟩, ContinuousMap.tendsto_iff_tendstoUniformly.mpr ?_⟩
  simpa using hu

theorem sparse_continuousMap_signed_limit {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (v : ℕ → C(X, ℝ)) (w σ : ℕ → ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : ∀ n, 0 ≤ w n)
    (hwm : Antitone w) (hwlim : Tendsto w atTop (𝓝 0))
    (hσ : ∀ n, |σ n| ≤ 1) (hv : ∀ n x, |v n x| ≤ w n)
    (hdec : ∀ n m, n < m → ∀ x, v n x ≠ 0 → v m x ≠ 0 →
      w m ≤ q * w n) :
    ∃ f : C(X, ℝ), Tendsto (fun N => ∑ n ∈ range N, σ n • v n) atTop (𝓝 f) := by
  apply sparse_continuousMap_limit (fun n => σ n • v n) w hq0 hq1 hw0 hwm hwlim
  · intro n x
    change |σ n * v n x| ≤ w n
    rw [abs_mul]
    calc
      |σ n| * |v n x| ≤ 1 * w n :=
        mul_le_mul (hσ n) (hv n x) (abs_nonneg _) (by norm_num)
      _ = w n := one_mul _
  · intro n m hnm x hn hm
    apply hdec n m hnm x
    · intro h
      exact hn (by simp [h])
    · intro h
      exact hm (by simp [h])

/-- The final bump-family interface: arbitrary bounded signs times scalar weights
times continuous bumps converge in `C(X, ℝ)` under geometric overlap. -/
theorem sparse_continuousMap_weighted_limit {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (b : ℕ → C(X, ℝ)) (w σ : ℕ → ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : ∀ n, 0 ≤ w n)
    (hwm : Antitone w) (hwlim : Tendsto w atTop (𝓝 0))
    (hσ : ∀ n, |σ n| ≤ 1) (hb : ∀ n x, |b n x| ≤ 1)
    (hdec : ∀ n m, n < m → ∀ x, b n x ≠ 0 → b m x ≠ 0 →
      w m ≤ q * w n) :
    ∃ f : C(X, ℝ),
      Tendsto (fun N => ∑ n ∈ range N, σ n • (w n • b n)) atTop (𝓝 f) := by
  apply sparse_continuousMap_signed_limit (fun n => w n • b n) w σ
    hq0 hq1 hw0 hwm hwlim hσ
  · intro n x
    change |w n * b n x| ≤ w n
    rw [abs_mul, abs_of_nonneg (hw0 n)]
    simpa using mul_le_mul_of_nonneg_left (hb n x) (hw0 n)
  · intro n m hnm x hn hm
    apply hdec n m hnm x
    · intro h
      exact hn (by simp [h])
    · intro h
      exact hm (by simp [h])

end Erdos1151
