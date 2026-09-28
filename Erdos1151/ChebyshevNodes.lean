import Mathlib

/-!
Elementary arithmetic and separation of the actual Chebyshev nodes.
All proofs in this file are independent of external problem axioms.
-/

noncomputable section

namespace Erdos1151

def angle (n : ℕ) (k : Fin n) : ℝ :=
  ((2 * k.val + 1 : ℝ) * Real.pi) / (2 * n)

def node (n : ℕ) (k : Fin n) : ℝ := Real.cos (angle n k)

def Primitive (n : ℕ) (k : Fin n) : Prop := (2 * k.val + 1).Coprime n

theorem angle_pos (n : ℕ) (k : Fin n) : 0 < angle n k := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  unfold angle
  positivity

theorem angle_lt_pi (n : ℕ) (k : Fin n) : angle n k < Real.pi := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  have hk : (k.val : ℝ) + 1 ≤ n := by exact_mod_cast k.isLt
  unfold angle
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).2
  nlinarith [Real.pi_pos]

theorem angle_mem_Icc (n : ℕ) (k : Fin n) : angle n k ∈ Set.Icc 0 Real.pi :=
  ⟨(angle_pos n k).le, (angle_lt_pi n k).le⟩

theorem node_mem_Ioo (n : ℕ) (k : Fin n) : node n k ∈ Set.Ioo (-1) 1 := by
  constructor
  · simpa [node] using Real.strictAntiOn_cos (angle_mem_Icc n k)
      ⟨Real.pi_pos.le, le_rfl⟩ (angle_lt_pi n k)
  · simpa [node] using Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
      (angle_mem_Icc n k) (angle_pos n k)

theorem node_eq_iff_cross_mul {n m : ℕ} (k : Fin n) (j : Fin m) :
    node n k = node m j ↔ (2 * k.val + 1) * m = (2 * j.val + 1) * n := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt k.isLt)
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt j.isLt)
  have hcos : node n k = node m j ↔ angle n k = angle m j :=
    ⟨Real.strictAntiOn_cos.injOn (angle_mem_Icc n k) (angle_mem_Icc m j),
      fun h => congrArg Real.cos h⟩
  rw [hcos]
  unfold angle
  rw [div_eq_div_iff (by positivity : (2 : ℝ) * n ≠ 0)
    (by positivity : (2 : ℝ) * m ≠ 0)]
  constructor
  · intro h
    have h' : (2 * (k.val : ℝ) + 1) * m = (2 * (j.val : ℝ) + 1) * n := by
      nlinarith [Real.pi_pos]
    exact_mod_cast h'
  · intro h
    have h' : (2 * (k.val : ℝ) + 1) * m = (2 * (j.val : ℝ) + 1) * n := by
      exact_mod_cast h
    nlinarith [Real.pi_pos]

theorem node_injective (n : ℕ) : Function.Injective (node n) := by
  intro k j h
  have h' := (node_eq_iff_cross_mul k j).1 h
  have hn : n ≠ 0 := Nat.ne_zero_of_lt k.isLt
  have hc := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn) h'
  apply Fin.ext
  omega

/-- A primitive node cannot occur in a strictly smaller positive row. -/
theorem primitive_ne_earlier {n m : ℕ} (k : Fin n) (j : Fin m)
    (hk : Primitive n k) (hmn : m < n) : node n k ≠ node m j := by
  intro h
  have heq := (node_eq_iff_cross_mul k j).1 h
  have hd : n ∣ (2 * k.val + 1) * m := by rw [heq]; exact dvd_mul_left _ _
  have hdiv : n ∣ m := (hk.symm).dvd_of_dvd_mul_left hd
  exact (not_le_of_gt hmn) (Nat.le_of_dvd (Nat.zero_lt_of_lt j.isLt) hdiv)

theorem angle_lower (n : ℕ) (k : Fin n) : Real.pi / (2 * n) ≤ angle n k := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  unfold angle
  apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * n)).2
  nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) k.val]

theorem angle_upper (n : ℕ) (k : Fin n) :
    angle n k ≤ Real.pi - Real.pi / (2 * n) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  have hk : (k.val : ℝ) + 1 ≤ n := by exact_mod_cast k.isLt
  unfold angle
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).2
  have hp : Real.pi / (2 * n) * (2 * n) = Real.pi :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith [Real.pi_pos]

/-- Two distinct rows' rational angles are separated by their denominator product. -/
theorem angle_gap {n m : ℕ} (k : Fin n) (j : Fin m)
    (hne : node n k ≠ node m j) :
    Real.pi / (2 * n * m) ≤ |angle n k - angle m j| := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  have hm : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hcross : (2 * k.val + 1) * m ≠ (2 * j.val + 1) * n :=
    fun h => hne ((node_eq_iff_cross_mul k j).2 h)
  have hgap : (1 : ℝ) ≤ |(((2 * k.val + 1) * m : ℕ) : ℝ) - ((2 * j.val + 1) * n : ℕ)| := by
    rcases lt_or_gt_of_ne hcross with h | h
    · have hr : (((2 * k.val + 1) * m : ℕ) : ℝ) + 1 ≤ ((2 * j.val + 1) * n : ℕ) := by
        exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hr : (((2 * j.val + 1) * n : ℕ) : ℝ) + 1 ≤ ((2 * k.val + 1) * m : ℕ) := by
        exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  have heq : angle n k - angle m j =
      ((((2 * k.val + 1) * m : ℕ) : ℝ) - ((2 * j.val + 1) * n : ℕ)) *
        (Real.pi / (2 * n * m)) := by
    unfold angle
    push_cast
    field_simp
  rw [heq, abs_mul, abs_of_pos (by positivity : 0 < Real.pi / (2 * n * m))]
  nlinarith [show 0 < Real.pi / (2 * n * m) by positivity]

/-- The elementary chord lower bound, expressed by distance from both endpoints. -/
theorem sin_lower_of_margin {t δ : ℝ} (hδ : 0 ≤ δ)
    (hleft : δ ≤ t) (hright : t ≤ Real.pi - δ) :
    2 / Real.pi * δ ≤ Real.sin t := by
  by_cases ht : t ≤ Real.pi / 2
  · exact (mul_le_mul_of_nonneg_left hleft (by positivity)).trans
      (Real.mul_le_sin (by linarith) ht)
  · have hs := Real.mul_le_sin (x := Real.pi - t) (by linarith) (by linarith)
    rw [Real.sin_pi_sub] at hs
    exact (mul_le_mul_of_nonneg_left (by linarith : δ ≤ Real.pi - t)
      (by positivity)).trans hs

theorem angle_bounds_of_le {n N : ℕ} (k : Fin n) (hnN : n ≤ N) :
    Real.pi / (2 * N) ≤ angle n k ∧ angle n k ≤ Real.pi - Real.pi / (2 * N) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  have hN : 0 < (N : ℝ) := lt_of_lt_of_le hn (by exact_mod_cast hnN)
  have hle : Real.pi / (2 * N) ≤ Real.pi / (2 * n) := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
    exact_mod_cast (Nat.mul_le_mul_left 2 hnN)
  exact ⟨hle.trans (angle_lower n k), (angle_upper n k).trans (by linarith)⟩

/-- Uniform cubic separation for all unequal nodes from rows bounded by `N`. -/
theorem node_separation {n m N : ℕ} (k : Fin n) (j : Fin m)
    (hnN : n ≤ N) (hmN : m ≤ N) (hne : node n k ≠ node m j) :
    1 / (N : ℝ) ^ 3 ≤ |node n k - node m j| := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  have hm : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hN : 0 < (N : ℝ) := lt_of_lt_of_le hn hnN'
  obtain ⟨ha₁, ha₂⟩ := angle_bounds_of_le k hnN
  obtain ⟨hb₁, hb₂⟩ := angle_bounds_of_le j hmN
  have havg : 1 / (N : ℝ) ≤ Real.sin ((angle n k + angle m j) / 2) := by
    have hs := sin_lower_of_margin (δ := Real.pi / (2 * N)) (by positivity)
      (t := (angle n k + angle m j) / 2) (by linarith) (by linarith)
    convert hs using 1 <;> field_simp
  have hdiff : 1 / (2 * (n : ℝ) * m) ≤ |Real.sin ((angle n k - angle m j) / 2)| := by
    have hbound : |(angle n k - angle m j) / 2| ≤ Real.pi / 2 := by
      rw [abs_le]
      constructor <;> linarith [angle_pos n k, angle_pos m j,
        angle_lt_pi n k, angle_lt_pi m j]
    have hs := Real.mul_abs_le_abs_sin hbound
    have hg := angle_gap k j hne
    have heq : 2 / Real.pi * |(angle n k - angle m j) / 2| =
        |angle n k - angle m j| / Real.pi := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    rw [heq] at hs
    have hdiv := div_le_div_of_nonneg_right hg Real.pi_pos.le
    have hc : (Real.pi / (2 * n * m)) / Real.pi = 1 / (2 * (n : ℝ) * m) := by
      field_simp
    rw [hc] at hdiv
    exact hdiv.trans hs
  have hprod : 1 / ((N : ℝ) * n * m) ≤ |node n k - node m j| := by
    rw [node, node, Real.cos_sub_cos, abs_mul, abs_mul,
      abs_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0), neg_neg,
      abs_of_nonneg (le_trans (by positivity) havg)]
    have hp := mul_le_mul havg hdiff (by positivity)
      (le_trans (by positivity : (0 : ℝ) ≤ 1 / N) havg)
    calc
      1 / ((N : ℝ) * n * m) = 2 * (1 / N * (1 / (2 * n * m))) := by field_simp
      _ ≤ 2 * (Real.sin ((angle n k + angle m j) / 2) *
          |Real.sin ((angle n k - angle m j) / 2)|) := by gcongr
      _ = _ := by ring
  apply le_trans _ hprod
  apply one_div_le_one_div_of_le (by positivity)
  calc
    (N : ℝ) * n * m ≤ (N : ℝ) * N * N := by gcongr
    _ = (N : ℝ) ^ 3 := by ring

end Erdos1151
