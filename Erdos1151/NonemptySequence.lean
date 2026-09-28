import Mathlib

/-!
Independent topological part of the nonempty closed-set construction.
The dense sequence is repeated using the natural-number pairing function;
every one of its values therefore occurs arbitrarily late.
-/

noncomputable section
open Filter Topology Set

namespace Erdos1151.NonemptyAssembly

/-- Every nonempty closed subset of the reals is the exact finite cluster set
of a sequence whose terms all belong to that set. -/
theorem exists_sequence_clusterSet (A : Set ℝ) (hA : IsClosed A) (hne : A.Nonempty) :
    ∃ a : ℕ → ℝ, (∀ n, a n ∈ A) ∧
      ∀ x, MapClusterPt x atTop a ↔ x ∈ A := by
  letI : Nonempty A := hne.to_subtype
  let d : ℕ → A := TopologicalSpace.denseSeq A
  let a : ℕ → ℝ := fun n => d (Nat.unpair n).1
  refine ⟨a, fun n => (d _).property, ?_⟩
  intro x
  constructor
  · intro hx
    exact hA.mem_of_mapClusterPt hx (Eventually.of_forall fun n => (d _).property)
  · intro hx
    rw [mapClusterPt_atTop_iff_forall_mem_closure]
    intro N
    have hden : DenseRange (fun n => (d n : A)) := TopologicalSpace.denseRange_denseSeq A
    have hxcl : (⟨x, hx⟩ : A) ∈ closure (Set.range d) := hden _
    have hxcl' : x ∈ closure ((Subtype.val : A → ℝ) '' Set.range d) :=
      mem_closure_image continuous_subtype_val.continuousAt hxcl
    apply closure_mono (s := (Subtype.val : A → ℝ) '' Set.range d) ?_ hxcl'
    rintro y ⟨z, ⟨k, rfl⟩, rfl⟩
    refine ⟨Nat.pair k N, Nat.right_le_pair k N, ?_⟩
    simp [a, Nat.unpair_pair]

/-- Exact interpolation on selected rows plus convergence to a point of `A`
on the complementary rows gives exactly the prescribed cluster set. -/
theorem clusterSet_of_selected_and_complement
    {u a : ℕ → ℝ} {rows : ℕ → ℕ} {A : Set ℝ} {c : ℝ}
    (hrows : StrictMono rows) (hclosed : IsClosed A) (hc : c ∈ A)
    (ha : ∀ x, MapClusterPt x atTop a ↔ x ∈ A)
    (hain : ∀ n, a n ∈ A)
    (hselected : ∀ n, u (rows n) = a n)
    (hother : Tendsto u (atTop ⊓ 𝓟 (Set.range rows)ᶜ) (𝓝 c)) :
    ∀ x, MapClusterPt x atTop u ↔ x ∈ A := by
  intro x
  constructor
  · intro hx
    have hsplit : (atTop : Filter ℕ) =
        (atTop ⊓ 𝓟 (Set.range rows)) ⊔ (atTop ⊓ 𝓟 (Set.range rows)ᶜ) := by
      rw [← inf_sup_left, Filter.sup_principal]
      simp
    rw [MapClusterPt, hsplit, Filter.map_sup, clusterPt_sup] at hx
    rcases hx with hx | hx
    · apply hclosed.mem_of_mapClusterPt hx
      filter_upwards [show ∀ᶠ n in atTop ⊓ 𝓟 (Set.range rows), n ∈ Set.range rows
        from Filter.eventually_inf_principal.mpr (Eventually.of_forall fun n hn => hn)] with n hn
      obtain ⟨m, rfl⟩ := hn
      rw [hselected]
      exact hain m
    · have hxc : x = c := by
        apply eq_of_nhds_neBot
        exact hx.mono hother
      simpa [hxc] using hc
  · intro hx
    have ha' := (ha x).mpr hx
    have hcomp : u ∘ rows = a := funext hselected
    apply MapClusterPt.of_comp hrows.tendsto_atTop
    simpa [hcomp] using ha'

end Erdos1151.NonemptyAssembly
