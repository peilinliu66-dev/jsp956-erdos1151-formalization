import Erdos1151.ChebyshevWeights
import Erdos1151.HarmonicCounting
import Erdos1151.TentChebyshev
import Erdos1151.PrimitiveCounting

noncomputable section

namespace Erdos1151

/-- The `m`-th root weakly to the right of the target angle. We use `m ≥ 1`. -/
def shellIndex (θ : ℝ) (n m : ℕ) : ℕ := ⌊(n : ℝ) * θ / Real.pi + 1 / 2⌋₊ + m - 1

theorem shellIndex_injective (θ : ℝ) (n : ℕ) :
    Set.InjOn (shellIndex θ n) (Set.Ici 1) := by
  intro a ha b hb heq
  unfold shellIndex at heq
  simp only [Set.mem_Ici] at ha hb
  omega

theorem shellIndex_image_Ico (θ : ℝ) (n L M : ℕ) (hL : 1 ≤ L) :
    (Finset.Ico L (L + M)).image (shellIndex θ n) =
      Finset.Ico (shellIndex θ n L) (shellIndex θ n L + M) := by
  ext k
  simp only [Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨m, ⟨hm₁, hm₂⟩, rfl⟩
    unfold shellIndex
    constructor <;> omega
  · intro hk
    refine ⟨L + (k - shellIndex θ n L), ?_, ?_⟩
    · omega
    · unfold shellIndex at *
      omega

theorem shell_primitive_count (θ : ℝ) (n L M : ℕ) (hL : 1 ≤ L) :
    (((Finset.Ico L (L + M)).filter fun m => (2 * shellIndex θ n m + 1).Coprime n).card) =
      (((Finset.Ico (shellIndex θ n L) (shellIndex θ n L + M)).filter
        fun k => (2 * k + 1).Coprime n).card) := by
  classical
  rw [← shellIndex_image_Ico θ n L M hL, Finset.filter_image]
  apply (Finset.card_image_iff.mpr ?_).symm
  intro a ha b hb hab
  have ha' := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).1
  have hb' := (Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1).1
  exact shellIndex_injective θ n (by simpa using hL.trans ha') (by simpa using hL.trans hb') hab

theorem shellIndex_cast (θ : ℝ) (n m : ℕ) (hm : 1 ≤ m) :
    (shellIndex θ n m : ℝ) =
      (⌊(n : ℝ) * θ / Real.pi + 1 / 2⌋₊ : ℝ) + m - 1 := by
  unfold shellIndex
  rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]

theorem shell_raw_angle_bounds (θ : ℝ) (n m : ℕ)
    (hθ : 0 ≤ θ) (hn : 0 < n) (hm : 1 ≤ m) :
    θ < (2 * (shellIndex θ n m : ℝ) + 1) * Real.pi / (2 * n) ∧
    (2 * (shellIndex θ n m : ℝ) + 1) * Real.pi / (2 * n) ≤
      θ + Real.pi * m / n := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : 0 ≤ (n : ℝ) * θ / Real.pi + 1 / 2 := by positivity
  have hlo := Nat.lt_floor_add_one ((n : ℝ) * θ / Real.pi + 1 / 2)
  have hhi := Nat.floor_le ha
  have hcancel : (n : ℝ) * θ / Real.pi * Real.pi = n * θ :=
    div_mul_cancel₀ _ Real.pi_ne_zero
  rw [shellIndex_cast θ n m hm]
  constructor
  · apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)).2
    have hmulp := mul_lt_mul_of_pos_right hlo Real.pi_pos
    nlinarith
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).2
    have hmulp := mul_le_mul_of_nonneg_right hhi Real.pi_pos.le
    have heq : Real.pi * m / n * (n : ℝ) = Real.pi * m := div_mul_cancel₀ _ hnr.ne'
    nlinarith

theorem shellIndex_lt (θ : ℝ) (n m : ℕ)
    (hθ : 0 ≤ θ) (hn : 0 < n) (hm : 1 ≤ m)
    (hroom : θ + Real.pi * m / n < Real.pi) : shellIndex θ n m < n := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hangle := (shell_raw_angle_bounds θ n m hθ hn hm).2.trans_lt hroom
  have hmul := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).1 hangle
  have hcast : (shellIndex θ n m : ℝ) < n := by nlinarith [Real.pi_pos]
  exact_mod_cast hcast

theorem shell_angle_bounds (θ : ℝ) (n m : ℕ)
    (hθ : 0 ≤ θ) (hn : 0 < n) (hm : 1 ≤ m)
    (hroom : θ + Real.pi * m / n < Real.pi) :
    θ < angle n ⟨shellIndex θ n m, shellIndex_lt θ n m hθ hn hm hroom⟩ ∧
    angle n ⟨shellIndex θ n m, shellIndex_lt θ n m hθ hn hm hroom⟩ ≤
      θ + Real.pi * m / n :=
  shell_raw_angle_bounds θ n m hθ hn hm

theorem shell_coefficient_lower (θ η s : ℝ) (n m : ℕ)
    (hθ : 0 ≤ θ) (hn : 0 < n) (hm : 1 ≤ m)
    (hroom : θ + Real.pi * m / n < Real.pi)
    (hη : 0 ≤ η) (hs : 0 ≤ s)
    (hcos : η ≤ |Real.cos ((n : ℝ) * θ)|)
    (hsin : s ≤ Real.sin (angle n ⟨shellIndex θ n m, shellIndex_lt θ n m hθ hn hm hroom⟩)) :
    (η * s / Real.pi) / m ≤
      |coefficient n ⟨shellIndex θ n m, shellIndex_lt θ n m hθ hn hm hroom⟩ (Real.cos θ)| := by
  let k : Fin n := ⟨shellIndex θ n m, shellIndex_lt θ n m hθ hn hm hroom⟩
  obtain ⟨hlo, hhi⟩ := shell_angle_bounds θ n m hθ hn hm hroom
  have hθpi : θ ≤ Real.pi := by linarith [angle_lt_pi n k]
  have hne : Real.cos θ ≠ node n k :=
    ne_of_gt (Real.strictAntiOn_cos ⟨hθ, hθpi⟩ (angle_mem_Icc n k) hlo)
  have hdist : |θ - angle n k| ≤ Real.pi * m / n := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm0 : (m : ℝ) > 0 := by exact_mod_cast (by omega : 0 < m)
  have hh := coefficient_lower_of_angle_distance n k θ η s (Real.pi * m / n)
    hne hη hs (by positivity) hcos hsin hdist
  convert hh using 1 <;> field_simp

/-- A fixed positive-width interior window, uniform in the interpolation degree. -/
def shellFraction (θ : ℝ) : ℝ := (Real.pi - θ) / (2 * Real.pi)

theorem shellFraction_pos {θ : ℝ} (hθ : θ < Real.pi) : 0 < shellFraction θ := by
  unfold shellFraction
  positivity

theorem shell_room_of_fraction (θ : ℝ) (n m : ℕ) (hn : 0 < n)
    (hθ : θ < Real.pi) (hm : (m : ℝ) ≤ shellFraction θ * n) :
    θ + Real.pi * m / n < Real.pi := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hfrac : Real.pi * (shellFraction θ * n) / n = (Real.pi - θ) / 2 := by
    unfold shellFraction
    field_simp
  have hle : Real.pi * m / n ≤ (Real.pi - θ) / 2 := by
    rw [← hfrac]
    gcongr
  linarith

theorem shell_sine_lower (θ : ℝ) (n m : ℕ)
    (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) (hn : 0 < n) (hm : 1 ≤ m)
    (hrange : (m : ℝ) ≤ shellFraction θ * n) :
    2 / Real.pi * min θ ((Real.pi - θ) / 2) ≤
      Real.sin (angle n ⟨shellIndex θ n m,
        shellIndex_lt θ n m hθ₀.le hn hm (shell_room_of_fraction θ n m hn hθπ hrange)⟩) := by
  let hr := shell_room_of_fraction θ n m hn hθπ hrange
  obtain ⟨hlo, hhi⟩ := shell_angle_bounds θ n m hθ₀.le hn hm hr
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hfrac : Real.pi * (shellFraction θ * n) / n = (Real.pi - θ) / 2 := by
    unfold shellFraction
    field_simp
  have hle : Real.pi * m / n ≤ (Real.pi - θ) / 2 := by
    rw [← hfrac]
    gcongr
  apply sin_lower_of_margin (le_min hθ₀.le (by linarith))
  · exact (min_le_left _ _).trans hlo.le
  · linarith [min_le_right θ ((Real.pi - θ) / 2)]

/-- Interior reciprocal mass embeds into the actual primitive Lagrange mass. -/
theorem primitiveMass_ge_shell_reciprocal (θ η : ℝ) (n M B : ℕ)
    (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) (hn : 0 < n) (hM : 1 ≤ M)
    (hB : (B : ℝ) ≤ shellFraction θ * n) (hη : 0 ≤ η)
    (hcos : η ≤ |Real.cos ((n : ℝ) * θ)|) :
    (η * (2 / Real.pi * min θ ((Real.pi - θ) / 2)) / Real.pi) *
      goodReciprocalSum (fun m => (2 * shellIndex θ n m + 1).Coprime n) M B ≤
      primitiveMass n (fun k => coefficient n k (Real.cos θ)) := by
  classical
  let S := (Finset.Ico M B).filter fun m => (2 * shellIndex θ n m + 1).Coprime n
  let F : ℕ → Fin n := fun m => ⟨shellIndex θ n m % n, Nat.mod_lt _ hn⟩
  have hmem : ∀ m ∈ S, M ≤ m ∧ m < B := by
    intro m hm
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1
  have hmr : ∀ m ∈ S, (m : ℝ) ≤ shellFraction θ * n := by
    intro m hm
    have hmB : (m : ℝ) ≤ B := by exact_mod_cast (hmem m hm).2.le
    exact hmB.trans hB
  have hidx : ∀ m ∈ S, shellIndex θ n m < n := by
    intro m hm
    exact shellIndex_lt θ n m hθ₀.le hn (hM.trans (hmem m hm).1)
      (shell_room_of_fraction θ n m hn hθπ (hmr m hm))
  have hF : ∀ m ∈ S, (F m).val = shellIndex θ n m := by
    intro m hm
    exact Nat.mod_eq_of_lt (hidx m hm)
  have hFinj : Set.InjOn F S := by
    intro a ha b hb hab
    have hc := congrArg Fin.val hab
    rw [hF a ha, hF b hb] at hc
    exact shellIndex_injective θ n (hM.trans (hmem a ha).1) (hM.trans (hmem b hb).1) hc
  have hsub : S.image F ⊆ primitiveNodes n := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
    rw [mem_primitiveNodes, Primitive, hF m hm]
    exact (Finset.mem_filter.mp hm).2
  have hterm : ∀ m ∈ S,
      (η * (2 / Real.pi * min θ ((Real.pi - θ) / 2)) / Real.pi) / m ≤
        |coefficient n (F m) (Real.cos θ)| := by
    intro m hm
    have hm1 := hM.trans (hmem m hm).1
    have hr := shell_room_of_fraction θ n m hn hθπ (hmr m hm)
    have heq : F m = ⟨shellIndex θ n m, shellIndex_lt θ n m hθ₀.le hn hm1 hr⟩ :=
      Fin.ext (hF m hm)
    rw [heq]
    apply shell_coefficient_lower θ η _ n m hθ₀.le hn hm1 hr hη
      (by positivity) hcos
    exact shell_sine_lower θ n m hθ₀ hθπ hn hm1 (hmr m hm)
  calc
    _ = ∑ m ∈ S, (η * (2 / Real.pi * min θ ((Real.pi - θ) / 2)) / Real.pi) / m := by
      simp [goodReciprocalSum, S, Finset.mul_sum, div_eq_mul_inv]
    _ ≤ ∑ m ∈ S, |coefficient n (F m) (Real.cos θ)| := Finset.sum_le_sum hterm
    _ = ∑ k ∈ S.image F, |coefficient n k (Real.cos θ)| := by
      rw [Finset.sum_image hFinj]
    _ ≤ primitiveMass n (fun k => coefficient n k (Real.cos θ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro k hk hnot
      exact abs_nonneg _

/-- The actual odd-prime sieve bound for the shifted Chebyshev window. -/
theorem shell_count_lower (θ : ℝ) (n L : ℕ) (hn : 0 < n) (hL : 1 ≤ L) :
    primitiveDensity n * (L : ℝ) - (2 : ℝ) ^ (oddPrimeFactors n).card ≤
      (((Finset.Ico L (2 * L)).filter
        fun m => (2 * shellIndex θ n m + 1).Coprime n).card : ℝ) := by
  rw [show 2 * L = L + L by omega, shell_primitive_count θ n L L hL]
  simpa only [mul_comm] using primitive_count_lower (shellIndex θ n L) L n hn

/-- Every arithmetic and interpolation term in this estimate is now explicit. -/
theorem primitiveMass_interior_log_lower (θ η : ℝ) (n : ℕ)
    (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) (hn : 1 ≤ n) (hη : 0 ≤ η)
    (hcos : η ≤ |Real.cos ((n : ℝ) * θ)|)
    (hcn : 2 ≤ shellFraction θ * (n : ℝ))
    (hlarge : 8 * (3 * Real.log 2 - Real.log (shellFraction θ)) ≤ Real.log (n : ℝ))
    (herr : 2 * (2 : ℝ) ^ (oddPrimeFactors n).card ≤
      primitiveDensity n * (n : ℝ) ^ (3 / 4 : ℝ)) :
    (η * (2 / Real.pi * min θ ((Real.pi - θ) / 2)) / Real.pi) *
      (primitiveDensity n * Real.log (n : ℝ) / (32 * Real.log 2)) ≤
      primitiveMass n (fun k => coefficient n k (Real.cos θ)) := by
  have hn0 : 0 < n := by omega
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hcut : 1 ≤ Nat.ceil ((n : ℝ) ^ (3 / 4 : ℝ)) := by
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnr _)
  have hh := reciprocal_three_quarter_lower_of_error
    (fun m => (2 * shellIndex θ n m + 1).Coprime n) n hn
    (shellFraction_pos hθπ) (primitiveDensity_pos n).le hcn hlarge
    (fun L hL => shell_count_lower θ n L hn0 (hcut.trans hL)) herr
  have hm := primitiveMass_ge_shell_reciprocal θ η n
    (Nat.ceil ((n : ℝ) ^ (3 / 4 : ℝ))) (Nat.floor (shellFraction θ * n))
    hθ₀ hθπ hn0 hcut (Nat.floor_le (by positivity)) hη hcos
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans hm

end Erdos1151
