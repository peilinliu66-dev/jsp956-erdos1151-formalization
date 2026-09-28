import Erdos1151.ChebyshevAtomNormalization
import Erdos1151.NonemptyMobius

/-! Shared finite angular data for the nonempty-target construction. -/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace Erdos1151.NonemptyAssembly

def oddLayers (R : ℕ) : Finset ℕ := (Finset.Icc 1 R).filter Odd

def finiteAtomSupport (n R : ℕ) : Finset ℝ :=
  (oddLayers R).biUnion (fun s => primitiveAtomSupport (n * s))

def finiteAtomValue (n R : ℕ) (θ α : ℝ) : ℝ :=
  ∑ s ∈ oddLayers R, layerAmplitude n s θ * primitiveAtom (n * s) θ α

@[simp] theorem mem_oddLayers (s R : ℕ) :
    s ∈ oddLayers R ↔ 1 ≤ s ∧ s ≤ R ∧ Odd s := by
  simp only [oddLayers, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem oddLayers_card_le (R : ℕ) : (oddLayers R).card ≤ R := by
  calc
    (oddLayers R).card ≤ (Finset.Icc 1 R).card := Finset.card_filter_le _ _
    _ = R := by simp

@[simp] theorem mem_finiteAtomSupport (n R : ℕ) (α : ℝ) :
    α ∈ finiteAtomSupport n R ↔
      ∃ s ∈ oddLayers R, α ∈ primitiveAtomSupport (n * s) := by
  classical
  exact Finset.mem_biUnion

theorem finiteAtomValue_zero_of_not_mem (n R : ℕ) (θ α : ℝ)
    (hα : α ∉ finiteAtomSupport n R) : finiteAtomValue n R θ α = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro s hs
  rw [primitiveAtom_zero_of_not_mem (n * s) θ α
    (fun ha => hα (Finset.mem_biUnion.mpr ⟨s, hs, ha⟩)), mul_zero]

theorem finiteAtomSupport_mem_Ioo {n R : ℕ} {α : ℝ}
    (hα : α ∈ finiteAtomSupport n R) : α ∈ Set.Ioo (0 : ℝ) Real.pi := by
  obtain ⟨s, _, hs⟩ := mem_finiteAtomSupport n R α |>.mp hα
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hs
  exact ⟨angle_pos _ _, angle_lt_pi _ _⟩

theorem finiteAtomSupport_subset_Ioo (n R : ℕ) :
    (finiteAtomSupport n R : Set ℝ) ⊆ Set.Ioo (0 : ℝ) Real.pi :=
  fun _ hα => finiteAtomSupport_mem_Ioo hα

theorem finiteAtomSupport_cos_ne {n R : ℕ} {θ α : ℝ}
    (hcos : ∀ d : ℕ, Real.cos ((d : ℝ) * θ) ≠ 0)
    (hα : α ∈ finiteAtomSupport n R) : Real.cos θ ≠ Real.cos α := by
  obtain ⟨s, _, hs⟩ := mem_finiteAtomSupport n R α |>.mp hα
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hs
  intro heq
  have hz := eval_T_node (n * s) k
  change Real.cos θ = node (n * s) k at heq
  rw [← heq, Polynomial.Chebyshev.T_real_cos] at hz
  push_cast at hz
  exact hcos (n * s) (by simpa only [Nat.cast_mul] using hz)

theorem finiteAtomSupport_cos_ne_of_uniform {n R : ℕ} {θ α κ : ℝ}
    (hκ : 0 < κ) (hcos : ∀ d : ℕ, κ ≤ |Real.cos ((d : ℝ) * θ)|)
    (hα : α ∈ finiteAtomSupport n R) : Real.cos θ ≠ Real.cos α := by
  apply finiteAtomSupport_cos_ne (hα := hα)
  intro d hd
  have h := hcos d
  rw [hd, abs_zero] at h
  linarith

theorem finiteAtomSupport_cos_ne_rational (p q n R : ℕ) (hq : Odd q)
    {α : ℝ} (hα : α ∈ finiteAtomSupport n R) :
    Real.cos (p * Real.pi / q) ≠ Real.cos α :=
  finiteAtomSupport_cos_ne (fun d => rational_cos_ne_zero p q d hq) hα

theorem finiteAtomValue_abs_le (n R : ℕ) (θ α κ M : ℝ)
    (hκ : 0 < κ) (hM : 0 < M)
    (hbase : κ ≤ |Real.cos ((n : ℝ) * θ)|)
    (hmass : ∀ s ∈ oddLayers R, M ≤ layerMass (n * s) θ) :
    |finiteAtomValue n R θ α| ≤ (R : ℝ) / (κ * M) := by
  classical
  have hterm (s : ℕ) (hs : s ∈ oddLayers R) :
      |layerAmplitude n s θ * primitiveAtom (n * s) θ α| ≤ 1 / (κ * M) := by
    have hs1 : 1 ≤ s := (mem_oddLayers s R).mp hs |>.1
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
    have hden : κ ≤ (s : ℝ) * κ := by nlinarith
    have hamp : |layerAmplitude n s θ| ≤ 1 / κ :=
      (layerAmplitude_abs_bound (by omega) hκ hbase).trans
        (one_div_le_one_div_of_le hκ hden)
    have hatom : |primitiveAtom (n * s) θ α| ≤ 1 / M :=
      (primitiveAtom_abs_le _ _ _ (hM.trans_le (hmass s hs))).trans
        (one_div_le_one_div_of_le hM (hmass s hs))
    rw [abs_mul]
    calc
      _ ≤ (1 / κ) * (1 / M) :=
        mul_le_mul hamp hatom (abs_nonneg _) (by positivity)
      _ = 1 / (κ * M) := by ring
  calc
    |finiteAtomValue n R θ α| ≤
        ∑ s ∈ oddLayers R, |layerAmplitude n s θ * primitiveAtom (n * s) θ α| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ oddLayers R, 1 / (κ * M) := Finset.sum_le_sum hterm
    _ = ((oddLayers R).card : ℝ) / (κ * M) := by simp [div_eq_mul_inv]
    _ ≤ (R : ℝ) / (κ * M) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast oddLayers_card_le R

/-- One sufficiently large base row makes every atom value small while
retaining positive normalization mass in every positive multiple layer. -/
theorem exists_large_finiteAtomValue_small (N R : ℕ) (θ κ ε : ℝ)
    (hκ : 0 < κ) (hε : 0 < ε)
    (hcos : ∀ d : ℕ, κ ≤ |Real.cos ((d : ℝ) * θ)|)
    (hmass : Tendsto (fun d => layerMass d θ) atTop atTop) :
    ∃ n > N, (∀ s : ℕ, 1 ≤ s → 0 < layerMass (n * s) θ) ∧
      ∀ α : ℝ, |finiteAtomValue n R θ α| ≤ ε := by
  let M : ℝ := ((R : ℝ) + 1) / (κ * ε)
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨n, hn, hlarge⟩ := exists_large_all_multiple_layerMass_ge θ M N hmass
  refine ⟨n, hn, fun s hs => hM.trans_le (hlarge s hs), ?_⟩
  intro α
  have hbound := finiteAtomValue_abs_le n R θ α κ M hκ hM (hcos n)
    (fun s hs => hlarge s ((mem_oddLayers s R).mp hs).1)
  apply hbound.trans
  apply (div_le_iff₀ (mul_pos hκ hM)).mpr
  have heq : ε * (κ * M) = (R : ℝ) + 1 := by
    dsimp [M]
    field_simp
  linarith

end Erdos1151.NonemptyAssembly
