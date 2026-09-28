import Mathlib

/-!
Finite, continuous tent families used by the corrected Erdős construction.
The results concern actual functions, not assumed interpolation responses.
-/

noncomputable section

open scoped BigOperators

namespace Erdos1151

/-- A tent of height one and radius `r`, centered at `a`. -/
def tent (r a x : ℝ) : ℝ := max 0 (1 - |x - a| / r)

theorem tent_nonneg (r a x : ℝ) : 0 ≤ tent r a x := le_max_left _ _

theorem tent_le_one {r : ℝ} (hr : 0 < r) (a x : ℝ) : tent r a x ≤ 1 := by
  apply max_le (by norm_num)
  exact sub_le_self _ (div_nonneg (abs_nonneg _) hr.le)

@[simp] theorem tent_center {r : ℝ} (a : ℝ) : tent r a a = 1 := by
  simp [tent]

theorem tent_eq_zero_iff {r a x : ℝ} (hr : 0 < r) :
    tent r a x = 0 ↔ r ≤ |x - a| := by
  rw [tent, max_eq_left_iff]
  constructor
  · intro h
    have : 1 ≤ |x - a| / r := by linarith
    simpa using (le_div_iff₀ hr).1 this
  · intro h
    have : 1 ≤ |x - a| / r := (le_div_iff₀ hr).2 (by simpa using h)
    linarith

theorem tent_ne_zero_iff {r a x : ℝ} (hr : 0 < r) :
    tent r a x ≠ 0 ↔ |x - a| < r := by
  rw [ne_eq, tent_eq_zero_iff hr, not_le]

@[fun_prop] theorem continuous_tent (r a : ℝ) : Continuous (tent r a) := by
  unfold tent
  fun_prop

/-- Unlike `Real.sign`, this sign never vanishes at zero. -/
def tentSign (w : ℝ) : ℝ := if 0 ≤ w then 1 else -1

@[simp] theorem abs_tentSign (w : ℝ) : |tentSign w| = 1 := by
  unfold tentSign
  split_ifs <;> norm_num

theorem mul_tentSign (w : ℝ) : w * tentSign w = |w| := by
  unfold tentSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

variable {ι : Type*} [DecidableEq ι]

/-- Signed tents only at the selected nodes. -/
def tentRow (P : Finset ι) (r : ℝ) (a w : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ P, tentSign (w i) * tent r (a i) x

theorem continuous_tentRow (P : Finset ι) (r : ℝ) (a w : ι → ℝ) :
    Continuous (tentRow P r a w) := by
  unfold tentRow
  fun_prop

theorem tentRow_zero_of_far (P : Finset ι) {r x : ℝ} (hr : 0 < r)
    (a w : ι → ℝ) (hfar : ∀ i ∈ P, r ≤ |x - a i|) :
    tentRow P r a w x = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [(tent_eq_zero_iff hr).2 (hfar i hi), mul_zero]

theorem tentRow_at_node (P : Finset ι) {r : ℝ} (hr : 0 < r)
    (a w : ι → ℝ) (j : ι)
    (hsep : ∀ i ∈ P, i ≠ j → r ≤ |a j - a i|) :
    tentRow P r a w (a j) = if j ∈ P then tentSign (w j) else 0 := by
  classical
  unfold tentRow
  by_cases hj : j ∈ P
  · rw [if_pos hj, Finset.sum_eq_single_of_mem j hj]
    · simp
    · intro i hi hij
      rw [(tent_eq_zero_iff hr).2 (hsep i hi hij), mul_zero]
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≠ j := by intro h; exact hj (h ▸ hi)
    rw [(tent_eq_zero_iff hr).2 (hsep i hi hij), mul_zero]

theorem tentRow_ne_zero_has_active (P : Finset ι) (r : ℝ) (a w : ι → ℝ) (x : ℝ)
    (hne : tentRow P r a w x ≠ 0) : ∃ i ∈ P, tent r (a i) x ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  apply Finset.sum_eq_zero
  intro i hi
  rw [h i hi, mul_zero]

theorem tentRow_abs_le_one (P : Finset ι) {r : ℝ} (hr : 0 < r)
    (a w : ι → ℝ)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → 2 * r ≤ |a i - a j|)
    (x : ℝ) : |tentRow P r a w x| ≤ 1 := by
  classical
  by_cases hz : tentRow P r a w x = 0
  · simp [hz]
  obtain ⟨i, hi, hactive⟩ := tentRow_ne_zero_has_active P r a w x hz
  have hi_close := (tent_ne_zero_iff hr).1 hactive
  have hj_zero (j : ι) (hj : j ∈ P) (hji : j ≠ i) : tent r (a j) x = 0 := by
    apply (tent_eq_zero_iff hr).2
    by_contra h
    have hj_close : |x - a j| < r := lt_of_not_ge h
    have hdist : |a i - a j| < 2 * r := by
      calc
        |a i - a j| ≤ |a i - x| + |x - a j| := abs_sub_le _ _ _
        _ = |x - a i| + |x - a j| := by rw [abs_sub_comm (a i) x]
        _ < 2 * r := by linarith
    exact (not_lt_of_ge (hsep i hi j hj (Ne.symm hji))) hdist
  have heq : tentRow P r a w x = tentSign (w i) * tent r (a i) x := by
    apply Finset.sum_eq_single_of_mem i hi
    intro j hj hji
    rw [hj_zero j hj hji, mul_zero]
  rw [heq, abs_mul, abs_tentSign, one_mul, abs_of_nonneg (tent_nonneg _ _ _)]
  exact tent_le_one hr _ _

/-- The weighted evaluation at its own nodes is exactly the selected absolute mass. -/
theorem tentRow_diagonal [Fintype ι] (P : Finset ι) {r : ℝ} (hr : 0 < r)
    (a w : ι → ℝ)
    (hsep : ∀ j, ∀ i ∈ P, i ≠ j → r ≤ |a j - a i|) :
    (∑ j, w j * tentRow P r a w (a j)) = ∑ j ∈ P, |w j| := by
  classical
  simp_rw [tentRow_at_node P hr a w _ (hsep _)]
  calc
    (∑ j, w j * if j ∈ P then tentSign (w j) else 0) =
        ∑ j, if j ∈ P then |w j| else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp [mul_tentSign]
    _ = ∑ j ∈ P, |w j| := by simp

/-- The same finite construction as an element of the compact continuous-function space. -/
def tentRowMap (P : Finset ι) (r : ℝ) (a w : ι → ℝ) :
    C(Set.Icc (-1 : ℝ) 1, ℝ) where
  toFun x := tentRow P r a w x.val
  continuous_toFun := (continuous_tentRow P r a w).comp continuous_subtype_val

@[simp] theorem tentRowMap_apply (P : Finset ι) (r : ℝ) (a w : ι → ℝ)
    (x : Set.Icc (-1 : ℝ) 1) : tentRowMap P r a w x = tentRow P r a w x.val := rfl

theorem tentRowMap_norm_le_one (P : Finset ι) {r : ℝ} (hr : 0 < r)
    (a w : ι → ℝ)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → 2 * r ≤ |a i - a j|) :
    ‖tentRowMap P r a w‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1)).2
  intro x
  exact tentRow_abs_le_one P hr a w hsep x.val

/-- Simultaneous activity forces a pair of selected centers to be close. -/
theorem tentRows_active_centers_close {κ : Type*} [DecidableEq κ]
    (P : Finset ι) (Q : Finset κ) {r s x : ℝ} (hr : 0 < r) (hs : 0 < s)
    (a w : ι → ℝ) (b v : κ → ℝ)
    (hP : tentRow P r a w x ≠ 0) (hQ : tentRow Q s b v x ≠ 0) :
    ∃ i ∈ P, ∃ j ∈ Q, |a i - b j| < r + s := by
  obtain ⟨i, hi, hai⟩ := tentRow_ne_zero_has_active P r a w x hP
  obtain ⟨j, hj, hbj⟩ := tentRow_ne_zero_has_active Q s b v x hQ
  refine ⟨i, hi, j, hj, ?_⟩
  calc
    |a i - b j| ≤ |a i - x| + |x - b j| := abs_sub_le _ _ _
    _ = |x - a i| + |x - b j| := by rw [abs_sub_comm (a i) x]
    _ < r + s := add_lt_add ((tent_ne_zero_iff hr).1 hai)
      ((tent_ne_zero_iff hs).1 hbj)

/-- Polynomially narrow radii suffice; no iterated exponentials are used. -/
def tentRadius (n : ℕ) : ℝ := 1 / (4 * (n : ℝ) ^ 6)

theorem tentRadius_pos {n : ℕ} (hn : 0 < n) : 0 < tentRadius n := by
  unfold tentRadius
  positivity

theorem tentRadius_antitone {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m) :
    tentRadius m ≤ tentRadius n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  unfold tentRadius
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn'.le hnm' 6) (by norm_num)

theorem two_tentRadius_le_inverse_cube {n : ℕ} (hn : 0 < n) :
    2 * tentRadius n ≤ 1 / (n : ℝ) ^ 3 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn'
  have hn0 : (0 : ℝ) < n := by linarith
  have hden : (n : ℝ) ^ 3 ≤ 2 * (n : ℝ) ^ 6 := by nlinarith [sq_nonneg ((n : ℝ) ^ 3)]
  calc
    2 * tentRadius n = 1 / (2 * (n : ℝ) ^ 6) := by
      unfold tentRadius
      field_simp
      ring
    _ ≤ 1 / (n : ℝ) ^ 3 := one_div_le_one_div_of_le (pow_pos hn0 3) hden

theorem tentRadius_sum_lt_inverse_cube {n m : ℕ}
    (hn : 0 < n) (hnm : n ≤ m) (hmn : m ≤ n ^ 2) :
    tentRadius n + tentRadius m < 1 / (m : ℝ) ^ 3 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le hn hnm
  have hmn' : (m : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hmn
  have hp : (m : ℝ) ^ 3 ≤ (n : ℝ) ^ 6 := by
    calc
      (m : ℝ) ^ 3 ≤ ((n : ℝ) ^ 2) ^ 3 := pow_le_pow_left₀ hm'.le hmn' 3
      _ = (n : ℝ) ^ 6 := by ring
  calc
    tentRadius n + tentRadius m ≤ 2 * tentRadius n := by
      linarith [tentRadius_antitone hn hnm]
    _ < 1 / (n : ℝ) ^ 6 := by
      unfold tentRadius
      have hnp : 0 < (n : ℝ) ^ 6 := pow_pos hn' 6
      field_simp
      nlinarith
    _ ≤ 1 / (m : ℝ) ^ 3 := one_div_le_one_div_of_le (pow_pos hm' 3) hp

/-- The distance bound supplied by Chebyshev-node separation implies square sparsity. -/
theorem tentRows_square_sparse {κ : Type*} [DecidableEq κ]
    (P : Finset ι) (Q : Finset κ) {n m : ℕ} (hn : 0 < n) (hnm : n < m)
    (a w : ι → ℝ) (b v : κ → ℝ) (x : ℝ)
    (hsep : ∀ i ∈ P, ∀ j ∈ Q, 1 / (m : ℝ) ^ 3 ≤ |a i - b j|)
    (hP : tentRow P (tentRadius n) a w x ≠ 0)
    (hQ : tentRow Q (tentRadius m) b v x ≠ 0) : n ^ 2 < m := by
  by_contra h
  have hmn : m ≤ n ^ 2 := Nat.le_of_not_gt h
  obtain ⟨i, hi, j, hj, hclose⟩ := tentRows_active_centers_close P Q
    (tentRadius_pos hn) (tentRadius_pos (lt_trans hn hnm)) a w b v hP hQ
  have hrad := tentRadius_sum_lt_inverse_cube hn hnm.le hmn
  exact (not_lt_of_ge (hsep i hi j hj)) (lt_trans hclose hrad)

end Erdos1151
