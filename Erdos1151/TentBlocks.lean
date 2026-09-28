import Erdos1151.Tent
import Erdos1151.ChebyshevWeights

/-!
Continuous finite-node extensions with quantitative control on all later
Chebyshev rows. This is the geometric part of the nonempty block construction.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1151

/-- Prescribed amplitudes, rather than only signs, at finitely many angular centers. -/
def amplitudeTents (P : Finset ℝ) (r : ℝ) (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ p ∈ P, v p * tent r p x

@[fun_prop] theorem continuous_amplitudeTents (P : Finset ℝ) (r : ℝ) (v : ℝ → ℝ) :
    Continuous (amplitudeTents P r v) := by
  unfold amplitudeTents
  fun_prop

theorem amplitudeTents_zero_of_far (P : Finset ℝ) {r x : ℝ} (hr : 0 < r)
    (v : ℝ → ℝ) (hfar : ∀ p ∈ P, r ≤ |x - p|) : amplitudeTents P r v x = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  rw [(tent_eq_zero_iff hr).2 (hfar p hp), mul_zero]

theorem amplitudeTents_at_center (P : Finset ℝ) {r : ℝ} (hr : 0 < r)
    (v : ℝ → ℝ) (p : ℝ) (hp : p ∈ P)
    (hsep : ∀ q ∈ P, q ≠ p → r ≤ |p - q|) : amplitudeTents P r v p = v p := by
  classical
  unfold amplitudeTents
  rw [Finset.sum_eq_single_of_mem p hp]
  · simp
  · intro q hq hqp
    rw [(tent_eq_zero_iff hr).2 (hsep q hq hqp), mul_zero]

/-- Counting an actual Chebyshev angular grid in an interval of radius `r`.
The additive one is independent of the row size and interval location. -/
theorem angle_grid_count {n : ℕ} (hn : 0 < n) (p r : ℝ) (hr : 0 ≤ r) :
    ((Finset.univ.filter fun k : Fin n => |angle n k - p| < r).card : ℝ)
      ≤ 2 * r * n / Real.pi + 1 := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun k => |angle n k - p| < r
  change (s.card : ℝ) ≤ _
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    let b := s.max' hs
    have ha : a ∈ s := s.min'_mem hs
    have hb : b ∈ s := s.max'_mem hs
    have hab : a ≤ b := s.min'_le b hb
    have hsub : s.image Fin.val ⊆ Finset.Icc a.val b.val := by
      intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_Icc.mpr ⟨s.min'_le j hj, s.le_max' j hj⟩
    have hcard : s.card ≤ b.val + 1 - a.val := by
      have h := Finset.card_le_card hsub
      simpa [Finset.card_image_of_injective _ Fin.val_injective] using h
    have hcardR : (s.card : ℝ) ≤ (b.val : ℝ) + 1 - a.val := by
      have hab' : a.val ≤ b.val + 1 := Nat.le_succ_of_le hab
      exact_mod_cast hcard
    have ha' : |angle n a - p| < r := (Finset.mem_filter.mp ha).2
    have hb' : |angle n b - p| < r := (Finset.mem_filter.mp hb).2
    have hgap : angle n b - angle n a < 2 * r := by
      have ha₁ := (abs_lt.mp ha').1
      have hb₂ := (abs_lt.mp hb').2
      linarith
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have heq : angle n b - angle n a = ((b.val : ℝ) - a.val) * Real.pi / n := by
      unfold angle
      field_simp
      ring
    rw [heq] at hgap
    have hdiff : (b.val : ℝ) - a.val < 2 * r * n / Real.pi := by
      apply (lt_div_iff₀ Real.pi_pos).2
      exact (div_lt_iff₀ hnR).1 hgap
    linarith
  · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [this, Finset.card_empty, Nat.cast_zero]
    positivity

/-- A node with fixed positive cosine distance from the evaluation point has
a uniformly bounded coefficient of order `1/n`. -/
theorem coefficient_upper_of_cos_distance (n : ℕ) (k : Fin n) (θ d : ℝ)
    (hd : 0 < d) (hgap : d ≤ |Real.cos θ - node n k|) :
    |coefficient n k (Real.cos θ)| ≤ 1 / ((n : ℝ) * d) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt k.isLt
  have hx : Real.cos θ ≠ node n k := sub_ne_zero.mp (abs_pos.mp (hd.trans_le hgap))
  rw [abs_coefficient_formula n k θ hx]
  calc
    |Real.cos ((n : ℝ) * θ)| * Real.sin (angle n k) /
        ((n : ℝ) * |Real.cos θ - node n k|) ≤
        1 / ((n : ℝ) * |Real.cos θ - node n k|) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        |Real.cos ((n : ℝ) * θ)| * Real.sin (angle n k) ≤ 1 * 1 :=
          mul_le_mul (Real.abs_cos_le_one _) (Real.sin_le_one _)
            (Real.sin_pos_of_mem_Ioo ⟨angle_pos n k, angle_lt_pi n k⟩).le (by norm_num)
        _ = 1 := by ring
    _ ≤ 1 / ((n : ℝ) * d) :=
      one_div_le_one_div_of_le (mul_pos hn hd) (mul_le_mul_of_nonneg_left hgap hn.le)

/-- Restricting the angular radius also preserves a cosine-distance margin. -/
theorem cos_distance_of_near_center {θ p x d r : ℝ}
    (hcenter : d ≤ |Real.cos θ - Real.cos p|) (hr : r ≤ d / 2)
    (hx : |x - p| < r) : d / 2 ≤ |Real.cos θ - Real.cos x| := by
  have hcos := Real.abs_cos_sub_cos_le x p
  have htri := abs_sub_le (Real.cos θ) (Real.cos x) (Real.cos p)
  linarith

theorem single_tent_evaluation_bound {n : ℕ} (hn : 0 < n) (θ p d r : ℝ)
    (hd : 0 < d) (hr : 0 < r) (hrd : r ≤ d / 2)
    (hp : d ≤ |Real.cos θ - Real.cos p|) :
    |∑ k : Fin n, coefficient n k (Real.cos θ) * tent r p (angle n k)| ≤
      (2 * r * n / Real.pi + 1) / ((n : ℝ) * (d / 2)) := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun k => |angle n k - p| < r
  have heq : (∑ k : Fin n, coefficient n k (Real.cos θ) * tent r p (angle n k)) =
      ∑ k ∈ s, coefficient n k (Real.cos θ) * tent r p (angle n k) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hks
    have hfar : r ≤ |angle n k - p| := by simpa [s, not_lt] using hks
    rw [(tent_eq_zero_iff hr).2 hfar, mul_zero]
  rw [heq]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    |∑ k ∈ s, coefficient n k (Real.cos θ) * tent r p (angle n k)| ≤
        ∑ k ∈ s, |coefficient n k (Real.cos θ) * tent r p (angle n k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ s, 1 / ((n : ℝ) * (d / 2)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hclose := (Finset.mem_filter.mp hk).2
      rw [abs_mul, abs_of_nonneg (tent_nonneg _ _ _)]
      calc
        |coefficient n k (Real.cos θ)| * tent r p (angle n k) ≤
            (1 / ((n : ℝ) * (d / 2))) * 1 :=
          mul_le_mul
            (coefficient_upper_of_cos_distance n k θ (d / 2) (by positivity)
              (cos_distance_of_near_center hp hrd hclose))
            (tent_le_one hr _ _) (tent_nonneg _ _ _) (by positivity)
        _ = _ := mul_one _
    _ = (s.card : ℝ) / ((n : ℝ) * (d / 2)) := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right (angle_grid_count hn p r hr.le) (by positivity)

/-- The entire large-row response is small, including any exact atom coincidences.
This is useful after choosing a finite intermediate block in advance. -/
theorem amplitudeTents_evaluation_bound (P : Finset ℝ) {n : ℕ} (hn : 0 < n)
    (θ d r V : ℝ) (v : ℝ → ℝ) (hd : 0 < d) (hr : 0 < r)
    (hrd : r ≤ d / 2) (hV : 0 ≤ V) (hv : ∀ p ∈ P, |v p| ≤ V)
    (hp : ∀ p ∈ P, d ≤ |Real.cos θ - Real.cos p|) :
    |∑ k : Fin n, coefficient n k (Real.cos θ) * amplitudeTents P r v (angle n k)| ≤
      (2 * V * P.card / d) * (2 * r / Real.pi + 1 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : (∑ k : Fin n, coefficient n k (Real.cos θ) * amplitudeTents P r v (angle n k)) =
      ∑ p ∈ P, v p * ∑ k : Fin n, coefficient n k (Real.cos θ) * tent r p (angle n k) := by
    simp only [amplitudeTents, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [heq]
  calc
    |∑ p ∈ P, v p * ∑ k : Fin n, coefficient n k (Real.cos θ) * tent r p (angle n k)| ≤
        ∑ p ∈ P, |v p * ∑ k : Fin n, coefficient n k (Real.cos θ) * tent r p (angle n k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, V * ((2 * r * n / Real.pi + 1) / ((n : ℝ) * (d / 2))) := by
      apply Finset.sum_le_sum
      intro p hp'
      rw [abs_mul]
      exact mul_le_mul (hv p hp')
        (single_tent_evaluation_bound hn θ p d r hd hr hrd (hp p hp'))
        (abs_nonneg _) hV
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp

/-- Uniformity in the entire infinite tail is explicit. -/
theorem amplitudeTents_after_cutoff (P : Finset ℝ) {K n : ℕ} (hK : 0 < K) (hKn : K ≤ n)
    (θ d r V : ℝ) (v : ℝ → ℝ) (hd : 0 < d) (hr : 0 < r)
    (hrd : r ≤ d / 2) (hV : 0 ≤ V) (hv : ∀ p ∈ P, |v p| ≤ V)
    (hp : ∀ p ∈ P, d ≤ |Real.cos θ - Real.cos p|) :
    |∑ k : Fin n, coefficient n k (Real.cos θ) * amplitudeTents P r v (angle n k)| ≤
      (2 * V * P.card / d) * (2 * r / Real.pi + 1 / (K : ℝ)) := by
  apply (amplitudeTents_evaluation_bound P (lt_of_lt_of_le hK hKn)
    θ d r V v hd hr hrd hV hv hp).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_right
  apply one_div_le_one_div_of_le
  · exact_mod_cast hK
  · exact_mod_cast hKn

theorem amplitudeTents_abs_le (P : Finset ℝ) {r V : ℝ} (hr : 0 < r)
    (v : ℝ → ℝ) (hV : 0 ≤ V) (hv : ∀ p ∈ P, |v p| ≤ V)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * r ≤ |p - q|)
    (x : ℝ) : |amplitudeTents P r v x| ≤ V := by
  classical
  by_cases ha : ∃ p ∈ P, tent r p x ≠ 0
  · obtain ⟨p, hp, hpx⟩ := ha
    have hpclose := (tent_ne_zero_iff hr).1 hpx
    have hzero (q : ℝ) (hq : q ∈ P) (hqp : q ≠ p) : tent r q x = 0 := by
      apply (tent_eq_zero_iff hr).2
      have hdist := hsep p hp q hq hqp.symm
      have htri := abs_sub_le p x q
      rw [abs_sub_comm p x] at htri
      linarith
    have heq : amplitudeTents P r v x = v p * tent r p x := by
      apply Finset.sum_eq_single_of_mem p hp
      intro q hq hqp
      rw [hzero q hq hqp, mul_zero]
    rw [heq, abs_mul, abs_of_nonneg (tent_nonneg _ _ _)]
    calc
      |v p| * tent r p x ≤ V * 1 :=
        mul_le_mul (hv p hp) (tent_le_one hr _ _) (tent_nonneg _ _ _) hV
      _ = V := mul_one V
  · push Not at ha
    have heq : amplitudeTents P r v x = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [ha p hp, mul_zero]
    simpa [heq] using hV

theorem amplitudeTents_at_finite_grid (P Q : Finset ℝ) {r : ℝ} (hr : 0 < r)
    (v : ℝ → ℝ)
    (hsep : ∀ x ∈ Q, ∀ p ∈ P, x ≠ p → r ≤ |x - p|)
    (x : ℝ) (hx : x ∈ Q) :
    amplitudeTents P r v x = if x ∈ P then v x else 0 := by
  classical
  by_cases hxp : x ∈ P
  · rw [if_pos hxp]
    apply amplitudeTents_at_center P hr v x hxp
    intro p hp hpx
    exact hsep x hx p hp hpx.symm
  · rw [if_neg hxp]
    apply amplitudeTents_zero_of_far P hr v
    intro p hp
    exact hsep x hx p hp (fun h => hxp (h ▸ hp))

private theorem finite_positive_lower_bound {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 < f a) : ∃ d : ℝ, 0 < d ∧ ∀ a ∈ s, d ≤ f a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s has ih =>
    obtain ⟨d, hd, hs⟩ := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    refine ⟨min d (f a), lt_min hd (hf a (Finset.mem_insert_self _ _)), ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hs b hb)

/-- An arbitrarily narrow radius preserves any prescribed finite table and
also makes all same-family tents disjoint. -/
theorem exists_amplitudeTents_radius (P Q : Finset ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ r : ℝ, 0 < r ∧ r ≤ r₀ ∧
      ∀ x ∈ Q ∪ P, ∀ p ∈ P, x ≠ p → 2 * r ≤ |x - p| := by
  classical
  let s := ((Q ∪ P).product P).filter fun z => z.1 ≠ z.2
  obtain ⟨d, hd, hdist⟩ := finite_positive_lower_bound s (fun z => |z.1 - z.2|) (by
    intro z hz
    exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hz).2))
  refine ⟨min r₀ (d / 2), lt_min hr₀ (by positivity), min_le_left _ _, ?_⟩
  intro x hx p hp hxp
  have h := hdist (x, p) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hp⟩, hxp⟩)
  have hr := min_le_right r₀ (d / 2)
  linarith

/-- Any finite set of centers avoiding the evaluation point admits a uniform
positive cosine-distance margin. -/
theorem finite_centers_cos_margin (P : Finset ℝ) (θ : ℝ)
    (hp : ∀ p ∈ P, Real.cos θ ≠ Real.cos p) :
    ∃ d : ℝ, 0 < d ∧ ∀ p ∈ P, d ≤ |Real.cos θ - Real.cos p| :=
  finite_positive_lower_bound P _ (fun p hp' => abs_pos.mpr (sub_ne_zero.mpr (hp p hp')))

theorem amplitudeTents_zero_near (P : Finset ℝ) (θ d r : ℝ) (v : ℝ → ℝ)
    (hr : 0 < r) (hrd : r ≤ d / 2)
    (hp : ∀ p ∈ P, d ≤ |Real.cos θ - Real.cos p|)
    (x : ℝ) (hx : |x - θ| < d / 2) : amplitudeTents P r v x = 0 := by
  apply amplitudeTents_zero_of_far P hr v
  intro p hp'
  have hcenter : d ≤ |θ - p| := (hp p hp').trans (Real.abs_cos_sub_cos_le θ p)
  have htri := abs_sub_le θ x p
  rw [abs_sub_comm θ x] at htri
  linarith

end Erdos1151
