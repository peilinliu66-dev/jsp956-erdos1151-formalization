import Erdos1151.TentBlocks
import Erdos1151.UniformAlternating
import Erdos1151.TentChebyshev
import Erdos1151.InterpolationOperator

/-! Converting finite angular atom data to actual continuous functions, with
uniform control of the infinite interpolation tail. -/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace Erdos1151

def angularGridThrough (K : ℕ) : Finset ℝ :=
  (Finset.range (K + 1)).biUnion fun n => Finset.univ.image (angle n)

theorem angle_mem_angularGridThrough {n K : ℕ} (hn : n ≤ K) (k : Fin n) :
    angle n k ∈ angularGridThrough K := by
  classical
  exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr (by omega),
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩

def angularBumpMap (P : Finset ℝ) (r : ℝ) (v : ℝ → ℝ) :
    C(Set.Icc (-1 : ℝ) 1, ℝ) where
  toFun x := amplitudeTents P r v (Real.arccos x.val)
  continuous_toFun := (continuous_amplitudeTents P r v).comp
    (Real.continuous_arccos.comp continuous_subtype_val)

theorem angularBumpMap_eval (P : Finset ℝ) (r : ℝ) (v : ℝ → ℝ)
    (n : ℕ) (θ : ℝ) :
    finiteEvaluation (nodePoint n) (fun k => coefficient n k (Real.cos θ))
      (angularBumpMap P r v) =
    ∑ k : Fin n, coefficient n k (Real.cos θ) * amplitudeTents P r v (angle n k) := by
  rw [finiteEvaluation_apply]
  apply Finset.sum_congr rfl
  intro k hk
  change coefficient n k (Real.cos θ) * amplitudeTents P r v
    (Real.arccos (Real.cos (angle n k))) = _
  rw [Real.arccos_cos (angle_pos n k).le (angle_lt_pi n k).le]

def atomicAngularEvaluation (P : Finset ℝ) (v : ℝ → ℝ) (θ : ℝ) (n : ℕ) : ℝ :=
  ∑ k : Fin n, coefficient n k (Real.cos θ) *
    if angle n k ∈ P then v (angle n k) else 0

/-- Quantitative continuous extension of a finite atom table.

The construction controls *all* interpolation rows: a finite initial block is
preserved exactly, and the full infinite tail is small. The fixed extension
also has interpolation values tending to zero, by alternating cancellation.
-/
theorem continuous_atomic_extension (P : Finset ℝ) (v : ℝ → ℝ) (θ V δ : ℝ)
    (hθ : θ ∈ Set.Icc 0 Real.pi) (hV : 0 ≤ V) (hδ : 0 < δ)
    (hv : ∀ p ∈ P, |v p| ≤ V)
    (havoid : ∀ p ∈ P, Real.cos θ ≠ Real.cos p) (N : ℕ) :
    ∃ K : ℕ, N < K ∧ ∃ ψ : C(Set.Icc (-1 : ℝ) 1, ℝ),
      ‖ψ‖ ≤ V ∧
      (∀ n ≤ K, finiteEvaluation (nodePoint n) (fun k => coefficient n k (Real.cos θ)) ψ =
        atomicAngularEvaluation P v θ n) ∧
      (∀ n, K < n → |finiteEvaluation (nodePoint n)
        (fun k => coefficient n k (Real.cos θ)) ψ| ≤ δ) ∧
      Tendsto (fun n => finiteEvaluation (nodePoint n)
        (fun k => coefficient n k (Real.cos θ)) ψ) atTop (𝓝 0) := by
  classical
  obtain ⟨d, hd, hmargin⟩ := finite_centers_cos_margin P θ havoid
  let A : ℝ := 2 * V * P.card / d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlim : Tendsto (fun n : ℕ => A / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by positivity : 0 < δ / 2)))
  let K := max K₀ (N + 1)
  have hNK : N < K := by dsimp [K]; omega
  have hKpos : 0 < K := by omega
  have hKsmall : A / (K : ℝ) < δ / 2 := hK₀ K (by dsimp [K]; omega)
  let r₀ := min (d / 2) (δ * Real.pi / (4 * (A + 1)))
  have hr₀ : 0 < r₀ := lt_min (by positivity) (by dsimp [A]; positivity)
  obtain ⟨r, hr, hrr₀, hsep⟩ := exists_amplitudeTents_radius P (angularGridThrough K) hr₀
  have hrd : r ≤ d / 2 := hrr₀.trans (min_le_left _ _)
  have hrδ : r ≤ δ * Real.pi / (4 * (A + 1)) := hrr₀.trans (min_le_right _ _)
  have hsmallr : A * (2 * r / Real.pi) ≤ δ / 2 := by
    have hden : 0 < 4 * (A + 1) := by positivity
    have hr' := (le_div_iff₀ hden).1 hrδ
    calc
      A * (2 * r / Real.pi) = (4 * A * r) / (2 * Real.pi) := by ring
      _ ≤ (δ * Real.pi) / (2 * Real.pi) :=
        div_le_div_of_nonneg_right (by nlinarith : 4 * A * r ≤ δ * Real.pi) (by positivity)
      _ = δ / 2 := by field_simp
  refine ⟨K, hNK, angularBumpMap P r v, ?_, ?_, ?_, ?_⟩
  · apply (ContinuousMap.norm_le _ hV).2
    intro x
    change |amplitudeTents P r v (Real.arccos x.val)| ≤ V
    apply amplitudeTents_abs_le P hr v hV hv
    intro p hp q hq hpq
    exact hsep p (Finset.mem_union_right _ hp) q hq hpq
  · intro n hn
    rw [angularBumpMap_eval]
    unfold atomicAngularEvaluation
    apply Finset.sum_congr rfl
    intro k hk
    rw [amplitudeTents_at_finite_grid P (angularGridThrough K) hr v]
    · intro x hx p hp hxp
      have h := hsep x (Finset.mem_union_left _ hx) p hp hxp
      linarith
    · exact angle_mem_angularGridThrough hn k
  · intro n hn
    rw [angularBumpMap_eval]
    have hb := amplitudeTents_after_cutoff P hKpos hn.le θ d r V v hd hr hrd hV hv hmargin
    apply hb.trans
    change A * (2 * r / Real.pi + 1 / (K : ℝ)) ≤ δ
    have hAeq : A * (1 / (K : ℝ)) = A / K := by ring
    rw [mul_add, hAeq]
    linarith
  · simp_rw [angularBumpMap_eval]
    exact chebyshev_offPoint_decay θ hθ (amplitudeTents P r v)
      (continuous_amplitudeTents P r v).continuousOn (by positivity : 0 < d / 2)
      (amplitudeTents_zero_near P θ d r v hr hrd hmargin)

/-- The finite algebraic spike requirements directly produce the genuine
continuous spike consumed by `BlockSelection.exists_blockFamily_of_spike`. -/
theorem continuous_spike_of_atomic (P : Finset ℝ) (v : ℝ → ℝ) (θ ε : ℝ)
    (hθ : θ ∈ Set.Icc 0 Real.pi) (hε : 0 < ε)
    (hv : ∀ p ∈ P, |v p| ≤ ε)
    (havoid : ∀ p ∈ P, Real.cos θ ≠ Real.cos p)
    (N n : ℕ) (hNn : N < n)
    (hdiag : atomicAngularEvaluation P v θ n = 1)
    (hzero : ∀ k ≤ N, atomicAngularEvaluation P v θ k = 0)
    (hoff : ∀ k, k ≠ n → |atomicAngularEvaluation P v θ k| ≤ ε) :
    ∃ ψ : C(Interval, ℝ), ‖ψ‖ ≤ ε ∧ chebyshevOperator (Real.cos θ) n ψ = 1 ∧
      (∀ k ≤ N, chebyshevOperator (Real.cos θ) k ψ = 0) ∧
      (∀ k, k ≠ n → |chebyshevOperator (Real.cos θ) k ψ| ≤ ε) ∧
      Tendsto (fun k => chebyshevOperator (Real.cos θ) k ψ) atTop (𝓝 0) := by
  obtain ⟨K, hnK, ψ, hnorm, htable, htail, hdecay⟩ :=
    continuous_atomic_extension P v θ ε ε hθ hε.le hε hv havoid n
  refine ⟨ψ, hnorm, ?_, ?_, ?_, hdecay⟩
  · exact (htable n hnK.le).trans hdiag
  · intro k hk
    exact (htable k (hk.trans (hNn.le.trans hnK.le))).trans (hzero k hk)
  · intro k hkn
    by_cases hk : k ≤ K
    · change |finiteEvaluation (nodePoint k) (fun i => coefficient k i (Real.cos θ)) ψ| ≤ ε
      rw [htable k hk]
      exact hoff k hkn
    · exact htail k (Nat.lt_of_not_ge hk)

end Erdos1151
