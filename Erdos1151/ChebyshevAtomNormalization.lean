import Erdos1151.ChebyshevMass

/-! Actual finite angular atoms, normalized by the proved primitive mass. -/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace Erdos1151.NonemptyAssembly

def layerMass (d : ℕ) (θ : ℝ) : ℝ :=
  primitiveMass d (fun k => coefficient d k (Real.cos θ))

def primitiveAtomSupport (d : ℕ) : Finset ℝ := (primitiveNodes d).image (angle d)

def primitiveAtom (d : ℕ) (θ α : ℝ) : ℝ :=
  ∑ k ∈ primitiveNodes d,
    if angle d k = α then tentSign (coefficient d k (Real.cos θ)) / layerMass d θ else 0

theorem angle_injective (d : ℕ) : Function.Injective (angle d) := by
  intro k j h
  apply node_injective d
  exact congrArg Real.cos h

theorem primitiveAtomSupport_mem_Ioo (d : ℕ) {α : ℝ} (hα : α ∈ primitiveAtomSupport d) :
    α ∈ Set.Ioo 0 Real.pi := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hα
  exact ⟨angle_pos d k, angle_lt_pi d k⟩

theorem primitiveAtomSupport_ne_evalAngle (d : ℕ) (θ : ℝ)
    (hcos : Real.cos ((d : ℝ) * θ) ≠ 0) {α : ℝ}
    (hα : α ∈ primitiveAtomSupport d) : α ≠ θ := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hα
  intro h
  have hz := eval_T_node d k
  rw [node, Polynomial.Chebyshev.T_real_cos] at hz
  push_cast at hz
  rw [h] at hz
  exact hcos hz

theorem primitiveAtom_at_angle (d : ℕ) (θ : ℝ) (k : Fin d) :
    primitiveAtom d θ (angle d k) =
      if k ∈ primitiveNodes d then tentSign (coefficient d k (Real.cos θ)) / layerMass d θ else 0 := by
  classical
  unfold primitiveAtom
  by_cases hk : k ∈ primitiveNodes d
  · rw [if_pos hk, Finset.sum_eq_single_of_mem k hk]
    · simp
    · intro j hj hjk
      rw [if_neg (fun h => hjk (angle_injective d h))]
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    intro h
    have hjk : j = k := angle_injective d h
    exact hk (hjk ▸ hj)

theorem primitiveAtom_zero_of_not_mem (d : ℕ) (θ α : ℝ)
    (hα : α ∉ primitiveAtomSupport d) : primitiveAtom d θ α = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k hk
  apply if_neg
  intro h
  exact hα (Finset.mem_image.mpr ⟨k, hk, h⟩)

theorem primitiveAtom_abs_le (d : ℕ) (θ α : ℝ) (hmass : 0 < layerMass d θ) :
    |primitiveAtom d θ α| ≤ 1 / layerMass d θ := by
  classical
  by_cases hα : α ∈ primitiveAtomSupport d
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hα
    rw [primitiveAtom_at_angle, if_pos hk, abs_div, abs_tentSign, abs_of_pos hmass]
  · rw [primitiveAtom_zero_of_not_mem d θ α hα, abs_zero]
    positivity

theorem primitiveAtom_diagonal (d : ℕ) (θ : ℝ) (hmass : layerMass d θ ≠ 0) :
    (∑ k : Fin d, coefficient d k (Real.cos θ) * primitiveAtom d θ (angle d k)) = 1 := by
  classical
  simp_rw [primitiveAtom_at_angle, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun k => k ∈ primitiveNodes d) = primitiveNodes d := by
    ext k
    simp
  rw [hfilter]
  simp_rw [← mul_div_assoc, mul_tentSign]
  rw [← Finset.sum_div]
  change layerMass d θ / layerMass d θ = 1
  exact div_self hmass

theorem layerMass_tendsto_of_lower (θ c : ℝ) (hc : 0 < c)
    (hmass : ∀ᶠ n : ℕ in atTop,
      c * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤ layerMass n θ) :
    Tendsto (fun n => layerMass n θ) atTop atTop := by
  apply tendsto_atTop_mono' _ hmass
  exact ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    log_nat_tendsto).const_mul_atTop hc

theorem layerMass_tendsto_interior (θ : ℝ) (hθ₀ : 0 < θ) (hθπ : θ < Real.pi)
    (hcos : ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, η ≤ |Real.cos ((n : ℝ) * θ)|) :
    Tendsto (fun n => layerMass n θ) atTop atTop := by
  obtain ⟨c, hc, hmass⟩ := exists_interior_mass_lower θ hθ₀ hθπ hcos
  exact layerMass_tendsto_of_lower θ c hc hmass

/-- One large base row controls all of its positive multiples simultaneously. -/
theorem eventually_all_multiple_layerMass_ge (θ A : ℝ)
    (hmass : Tendsto (fun n => layerMass n θ) atTop atTop) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, 1 ≤ s → A ≤ layerMass (n * s) θ := by
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (hmass.eventually (eventually_ge_atTop A)))
  filter_upwards [eventually_ge_atTop N] with n hn
  intro s hs
  exact hN (n * s) (hn.trans (Nat.le_mul_of_pos_right n (by omega)))

theorem exists_large_all_multiple_layerMass_ge (θ A : ℝ) (N : ℕ)
    (hmass : Tendsto (fun n => layerMass n θ) atTop atTop) :
    ∃ n > N, ∀ s : ℕ, 1 ≤ s → A ≤ layerMass (n * s) θ := by
  have h := (eventually_all_multiple_layerMass_ge θ A hmass).and
    (eventually_gt_atTop N)
  obtain ⟨n, hn, hN⟩ := h.exists
  exact ⟨n, hN, hn⟩

/-- All normalized primitive atoms on positive multiples can be made small
simultaneously. No finite cutoff or dyadic restriction is required. -/
theorem exists_large_all_multiple_primitiveAtom_small (θ ε : ℝ) (N : ℕ)
    (hε : 0 < ε) (hmass : Tendsto (fun n => layerMass n θ) atTop atTop) :
    ∃ n > N, ∀ s : ℕ, 1 ≤ s → 0 < layerMass (n * s) θ ∧
      ∀ α : ℝ, |primitiveAtom (n * s) θ α| ≤ ε := by
  obtain ⟨n, hn, hbound⟩ := exists_large_all_multiple_layerMass_ge θ (1 / ε) N hmass
  refine ⟨n, hn, fun s hs => ?_⟩
  have hp : 0 < layerMass (n * s) θ := (one_div_pos.mpr hε).trans_le (hbound s hs)
  refine ⟨hp, fun α => ?_⟩
  apply (primitiveAtom_abs_le (n * s) θ α hp).trans
  have hi := one_div_le_one_div_of_le (one_div_pos.mpr hε) (hbound s hs)
  simpa using hi

end Erdos1151.NonemptyAssembly
