import Erdos1151.NonemptyAtomResponse
import Erdos1151.NonemptyAtomData
import Erdos1151.TentBlockExtension

/-! All-row control of the actual finite Chebyshev atom table. -/

noncomputable section
open scoped BigOperators

namespace Erdos1151.NonemptyAssembly

def finiteAtomResponse (n R : ℕ) (θ : ℝ) (m : ℕ) : ℝ :=
  ∑ j : Fin m, coefficient m j (Real.cos θ) * finiteAtomValue n R θ (angle m j)

theorem finiteAtomResponse_eq_sum (n R : ℕ) (θ : ℝ) (m : ℕ) :
    finiteAtomResponse n R θ m =
      ∑ s ∈ oddLayers R, layerAmplitude n s θ * atomResponse m (n * s) θ := by
  unfold finiteAtomResponse finiteAtomValue atomResponse
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem finiteAtomResponse_of_not_odd_multiple {n m R : ℕ} (θ : ℝ)
    (hno : ¬∃ u, Odd u ∧ m = n * u) : finiteAtomResponse n R θ m = 0 := by
  rw [finiteAtomResponse_eq_sum]
  apply Finset.sum_eq_zero
  intro s hs
  rw [atomResponse_of_not_odd_multiple θ ?_, mul_zero]
  rintro ⟨t, ht, h⟩
  exact hno ⟨s * t, ((mem_oddLayers s R).mp hs).2.2.mul ht, by simpa [mul_assoc] using h⟩

theorem finiteAtomResponse_odd_multiple {n R u : ℕ} (hn : 0 < n) (hu : Odd u)
    (θ : ℝ) (hmass : ∀ s ∈ oddLayers R, layerMass (n * s) θ ≠ 0)
    (hcos : ∀ d : ℕ, Real.cos ((d : ℝ) * θ) ≠ 0)
    (hpoint : ∀ d : ℕ, ∀ k : Fin d, Real.cos θ ≠ node d k) :
    finiteAtomResponse n R θ (n * u) =
      ∑ s ∈ u.divisors.filter (fun s => s ≤ R),
        layerTransfer n u s θ * layerAmplitude n s θ := by
  rw [finiteAtomResponse_eq_sum]
  have hsub : u.divisors.filter (fun s => s ≤ R) ⊆ oddLayers R := by
    intro s hs
    obtain ⟨hdiv, hsR⟩ := Finset.mem_filter.mp hs
    have hsu := (Nat.mem_divisors.mp hdiv).1
    exact (mem_oddLayers s R).mpr
      ⟨Nat.pos_of_dvd_of_pos hsu hu.pos, hsR, hu.of_dvd_nat hsu⟩
  calc
    _ = ∑ s ∈ u.divisors.filter (fun s => s ≤ R),
        layerAmplitude n s θ * atomResponse (n * u) (n * s) θ := by
      symm
      apply Finset.sum_subset hsub
      intro s hs hsnot
      have hndvd : ¬s ∣ u := by
        intro hsu
        apply hsnot
        exact Finset.mem_filter.mpr
          ⟨Nat.mem_divisors.mpr ⟨hsu, hu.pos.ne'⟩, ((mem_oddLayers s R).mp hs).2.1⟩
      rw [atomResponse_layer_zero hn hndvd θ, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [atomResponse_layer hn hu
        (Nat.mem_divisors.mp (Finset.mem_filter.mp hs).1).1 θ
        (hmass s (hsub hs)) (hcos _) (hpoint _), mul_comm]

theorem finiteAtomResponse_diagonal {n R : ℕ} (hn : 0 < n) (hR : 1 ≤ R)
    (θ : ℝ) (hmass : ∀ s ∈ oddLayers R, layerMass (n * s) θ ≠ 0)
    (hcos : ∀ d : ℕ, Real.cos ((d : ℝ) * θ) ≠ 0)
    (hpoint : ∀ d : ℕ, ∀ k : Fin d, Real.cos θ ≠ node d k) :
    finiteAtomResponse n R θ n = 1 := by
  have h := finiteAtomResponse_odd_multiple (u := 1) hn (by norm_num) θ hmass hcos hpoint
  rw [mul_one] at h
  rw [h, finite_layer_delta (by norm_num) hR (hcos n) (fun s _ => hcos _)]
  simp

theorem finiteAtomResponse_before {n R m : ℕ} (θ : ℝ) (hm : m < n) :
    finiteAtomResponse n R θ m = 0 := by
  apply finiteAtomResponse_of_not_odd_multiple
  rintro ⟨u, hu, rfl⟩
  exact (not_lt_of_ge (Nat.le_mul_of_pos_right n hu.pos)) hm

theorem finiteAtomResponse_off_diagonal {n R m : ℕ} (hn : 0 < n) (hm : m ≠ n)
    (θ κ : ℝ) (hκ : 0 < κ)
    (hbase : κ ≤ |Real.cos ((n : ℝ) * θ)|)
    (hmass : ∀ s ∈ oddLayers R, layerMass (n * s) θ ≠ 0)
    (hcos : ∀ d : ℕ, Real.cos ((d : ℝ) * θ) ≠ 0)
    (hpoint : ∀ d : ℕ, ∀ k : Fin d, Real.cos θ ≠ node d k) :
    |finiteAtomResponse n R θ m| ≤ 1 / (κ * (R + 1)) := by
  by_cases hmul : ∃ u, Odd u ∧ m = n * u
  · obtain ⟨u, hu, rfl⟩ := hmul
    have hu1 : u ≠ 1 := by intro h; exact hm (by rw [h, mul_one])
    rw [finiteAtomResponse_odd_multiple hn hu θ hmass hcos hpoint]
    exact uniform_tail_layer_bound hu hu1 hκ hbase (fun s _ => hcos _)
  · rw [finiteAtomResponse_of_not_odd_multiple θ hmul, abs_zero]
    positivity

theorem atomicAngularEvaluation_finiteAtomValue (n R : ℕ) (θ : ℝ) (m : ℕ) :
    atomicAngularEvaluation (finiteAtomSupport n R) (finiteAtomValue n R θ) θ m =
      finiteAtomResponse n R θ m := by
  classical
  unfold atomicAngularEvaluation finiteAtomResponse
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hmem : angle m k ∈ finiteAtomSupport n R
  · rw [if_pos hmem]
  · rw [if_neg hmem, finiteAtomValue_zero_of_not_mem n R θ _ hmem]

end Erdos1151.NonemptyAssembly
