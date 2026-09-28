import Erdos1151.ChebyshevNodes

/-!
Lagrange interpolation coefficients at actual Chebyshev roots.
These proofs use mathlib's polynomial API directly. No external proof source is copied.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset

namespace Erdos1151

def coefficient (n : ℕ) (k : Fin n) (x : ℝ) : ℝ :=
  (Lagrange.basis Finset.univ (node n) k).eval x

def interpolation (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin n, f (node n k) * coefficient n k x

theorem coefficient_self (n : ℕ) (k : Fin n) : coefficient n k (node n k) = 1 := by
  exact Lagrange.eval_basis_self (node_injective n).injOn (Finset.mem_univ k)

theorem coefficient_other (n : ℕ) (k j : Fin n) (hkj : k ≠ j) :
    coefficient n k (node n j) = 0 :=
  Lagrange.eval_basis_of_ne hkj (Finset.mem_univ j)

theorem interpolation_at_node (n : ℕ) (f : ℝ → ℝ) (k : Fin n) :
    interpolation n f (node n k) = f (node n k) := by
  unfold interpolation
  rw [Finset.sum_eq_single k]
  · rw [coefficient_self, mul_one]
  · intro j hj hjk
    rw [coefficient_other n j k hjk, mul_zero]
  · simp

theorem interpolation_zero_on_nodes (n : ℕ) (f : ℝ → ℝ) (x : ℝ)
    (h : ∀ k : Fin n, f (node n k) = 0) : interpolation n f x = 0 := by
  simp [interpolation, h]

theorem interpolation_add (n : ℕ) (f g : ℝ → ℝ) (x : ℝ) :
    interpolation n (fun t => f t + g t) x = interpolation n f x + interpolation n g x := by
  simp [interpolation, add_mul, Finset.sum_add_distrib]

theorem interpolation_smul (n : ℕ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    interpolation n (fun t => c * f t) x = c * interpolation n f x := by
  simp [interpolation, Finset.mul_sum, mul_assoc]

theorem interpolation_bound (n : ℕ) (f : ℝ → ℝ) (x M : ℝ)
    (hf : ∀ k : Fin n, |f (node n k)| ≤ M) :
    |interpolation n f x| ≤ M * ∑ k : Fin n, |coefficient n k x| := by
  calc
    |interpolation n f x| ≤ ∑ k : Fin n, |f (node n k) * coefficient n k x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, M * |coefficient n k x| := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hf k) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem angle_mul_degree (n : ℕ) (k : Fin n) :
    (n : ℝ) * angle n k = k.val * Real.pi + Real.pi / 2 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt k.isLt)
  unfold angle
  field_simp

theorem sin_degree_angle (n : ℕ) (k : Fin n) :
    Real.sin ((n : ℝ) * angle n k) = (-1 : ℝ) ^ k.val := by
  rw [angle_mul_degree, Real.sin_add]
  simp [Real.cos_nat_mul_pi]

theorem eval_T_node (n : ℕ) (k : Fin n) : (T ℝ n).eval (node n k) = 0 := by
  rw [node, T_real_cos]
  push_cast
  rw [angle_mul_degree, Real.cos_add]
  simp

theorem chebyshev_nodal (n : ℕ) :
    T ℝ n = C ((2 : ℝ) ^ (n - 1)) * Lagrange.nodal Finset.univ (node n) := by
  have hd : Lagrange.nodal Finset.univ (node n) ∣ T ℝ n := by
    unfold Lagrange.nodal
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      exact Polynomial.pairwise_coprime_X_sub_C (node_injective n) hij
    · intro i hi
      exact Polynomial.dvd_iff_isRoot.mpr (eval_T_node n i)
  have hdegree : (T ℝ n).natDegree ≤ (Lagrange.nodal Finset.univ (node n)).natDegree := by
    simp
  simpa using Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (Lagrange.nodal_monic (s := Finset.univ) (v := node n)) hd hdegree

theorem eval_T_derivative_node (n : ℕ) (k : Fin n) :
    (Polynomial.derivative (T ℝ n)).eval (node n k) =
      (n : ℝ) * (-1 : ℝ) ^ k.val / Real.sin (angle n k) := by
  have hs : Real.sin (angle n k) ≠ 0 :=
    (Real.sin_pos_of_mem_Ioo ⟨angle_pos n k, angle_lt_pi n k⟩).ne'
  have hu' : (U ℝ ((n : ℤ) - 1)).eval (node n k) * Real.sin (angle n k) =
      (-1 : ℝ) ^ k.val := by
    rw [node, U_real_cos]
    push_cast
    simpa using sin_degree_angle n k
  rw [T_derivative_eq_U, eval_mul, eval_intCast]
  push_cast
  apply (eq_div_iff hs).2
  nlinarith [hu']

theorem coefficient_formula (n : ℕ) (k : Fin n) (θ : ℝ)
    (hne : Real.cos θ ≠ node n k) :
    coefficient n k (Real.cos θ) =
      Real.cos ((n : ℝ) * θ) * Real.sin (angle n k) /
        ((n : ℝ) * (Real.cos θ - node n k) * (-1 : ℝ) ^ k.val) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt k.isLt)
  have hc : (2 : ℝ) ^ (n - 1) ≠ 0 := by positivity
  have hs : Real.sin (angle n k) ≠ 0 :=
    (Real.sin_pos_of_mem_Ioo ⟨angle_pos n k, angle_lt_pi n k⟩).ne'
  have hp : (-1 : ℝ) ^ k.val ≠ 0 := by positivity
  have hd : Real.cos θ - node n k ≠ 0 := sub_ne_zero.mpr hne
  have heval : (2 : ℝ) ^ (n - 1) *
      (Lagrange.nodal Finset.univ (node n)).eval (Real.cos θ) =
      Real.cos ((n : ℝ) * θ) := by
    have h := congrArg (Polynomial.eval (Real.cos θ)) (chebyshev_nodal n)
    simpa [T_real_cos] using h.symm
  have hder : (2 : ℝ) ^ (n - 1) *
      (Polynomial.derivative (Lagrange.nodal Finset.univ (node n))).eval (node n k) =
      (n : ℝ) * (-1 : ℝ) ^ k.val / Real.sin (angle n k) := by
    rw [← eval_T_derivative_node]
    conv_rhs => rw [chebyshev_nodal]
    simp only [Polynomial.derivative_C_mul, eval_mul, eval_C]
  have hnval : (Lagrange.nodal Finset.univ (node n)).eval (Real.cos θ) =
      Real.cos ((n : ℝ) * θ) / (2 : ℝ) ^ (n - 1) :=
    (eq_div_iff hc).2 (by nlinarith [heval])
  have hdval : (Polynomial.derivative (Lagrange.nodal Finset.univ (node n))).eval (node n k) =
      ((n : ℝ) * (-1 : ℝ) ^ k.val / Real.sin (angle n k)) / (2 : ℝ) ^ (n - 1) :=
    (eq_div_iff hc).2 (by nlinarith [hder])
  unfold coefficient
  rw [Lagrange.eval_basis_not_at_node (Finset.mem_univ k) hne,
    Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ k), hnval, hdval]
  field_simp

theorem abs_coefficient_formula (n : ℕ) (k : Fin n) (θ : ℝ)
    (hne : Real.cos θ ≠ node n k) :
    |coefficient n k (Real.cos θ)| =
      |Real.cos ((n : ℝ) * θ)| * Real.sin (angle n k) /
        ((n : ℝ) * |Real.cos θ - node n k|) := by
  rw [coefficient_formula n k θ hne, abs_div, abs_mul, abs_mul, abs_mul]
  rw [abs_of_nonneg (Real.sin_pos_of_mem_Ioo ⟨angle_pos n k, angle_lt_pi n k⟩).le,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  simp

/-- An odd denominator is enough; the numerator need not be coprime or odd. -/
theorem rational_cos_ne_zero (p q n : ℕ) (hq : Odd q) :
    Real.cos ((n : ℝ) * (p * Real.pi / q)) ≠ 0 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.pos.ne'
  intro h
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp h
  have heqR : 2 * (n : ℝ) * p = (2 * (k : ℝ) + 1) * q := by
    field_simp at hk
    nlinarith [Real.pi_pos]
  have heq : 2 * (n : ℤ) * p = (2 * k + 1) * q := by exact_mod_cast heqR
  have heven : Even (2 * (n : ℤ) * p) := ⟨n * p, by ring⟩
  have hodd : Odd ((2 * k + 1) * (q : ℤ)) :=
    (show Odd (2 * k + 1) from ⟨k, by ring⟩).mul (by exact_mod_cast hq)
  rw [heq] at heven
  obtain ⟨a, ha⟩ := heven
  obtain ⟨b, hb⟩ := hodd
  omega

theorem rational_cos_mod (p q n : ℕ) (hq : 0 < q) :
    Real.cos ((n : ℝ) * (p * Real.pi / q)) =
      Real.cos (((n % (2 * q) : ℕ) : ℝ) * (p * Real.pi / q)) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have heq : (n : ℝ) * (p * Real.pi / q) =
      ((n % (2 * q) : ℕ) : ℝ) * (p * Real.pi / q) +
        ((n / (2 * q) * p : ℕ) : ℝ) * (2 * Real.pi) := by
    have hn := Nat.mod_add_div n (2 * q)
    have hn' : (n : ℝ) = (n % (2 * q) : ℕ) + 2 * q * (n / (2 * q) : ℕ) := by
      exact_mod_cast hn.symm
    push_cast
    rw [hn']
    field_simp
  rw [heq, Real.cos_add_nat_mul_two_pi]

/-- A single positive lower bound valid in every interpolation row. -/
theorem rational_cos_uniform_lower (p q : ℕ) (hq : Odd q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, δ ≤ |Real.cos ((n : ℝ) * (p * Real.pi / q))| := by
  have hfinite : ∀ N : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ n < N, δ ≤ |Real.cos ((n : ℝ) * (p * Real.pi / q))| := by
    intro N
    induction N with
    | zero => exact ⟨1, by norm_num, by simp⟩
    | succ N ih =>
      obtain ⟨δ, hδ, hbound⟩ := ih
      refine ⟨min δ |Real.cos ((N : ℝ) * (p * Real.pi / q))|,
        lt_min hδ (abs_pos.mpr (rational_cos_ne_zero p q N hq)), ?_⟩
      intro n hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
      · exact (min_le_left _ _).trans (hbound n hn)
      · exact min_le_right _ _
  obtain ⟨δ, hδ, hbound⟩ := hfinite (2 * q)
  refine ⟨δ, hδ, fun n => ?_⟩
  rw [rational_cos_mod p q n hq.pos]
  exact hbound _ (Nat.mod_lt _ (Nat.mul_pos (by norm_num) hq.pos))

theorem rational_point_not_node (p q n : ℕ) (hq : Odd q) (k : Fin n) :
    Real.cos (p * Real.pi / q) ≠ node n k := by
  intro h
  have hz := eval_T_node n k
  rw [← h, T_real_cos] at hz
  push_cast at hz
  exact rational_cos_ne_zero p q n hq hz

/-- A coefficient lower bound using only angular distance and a sine lower bound. -/
theorem coefficient_lower_of_angle_distance (n : ℕ) (k : Fin n) (θ δ s t : ℝ)
    (hne : Real.cos θ ≠ node n k) (hδ : 0 ≤ δ) (hs : 0 ≤ s) (ht : 0 < t)
    (hcos : δ ≤ |Real.cos ((n : ℝ) * θ)|) (hsin : s ≤ Real.sin (angle n k))
    (hdist : |θ - angle n k| ≤ t) :
    δ * s / ((n : ℝ) * t) ≤ |coefficient n k (Real.cos θ)| := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  have hx : 0 < |Real.cos θ - node n k| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hb : |Real.cos θ - node n k| ≤ t :=
    (Real.abs_cos_sub_cos_le θ (angle n k)).trans hdist
  rw [abs_coefficient_formula n k θ hne]
  calc
    δ * s / ((n : ℝ) * t) ≤ δ * s / ((n : ℝ) * |Real.cos θ - node n k|) :=
      div_le_div_of_nonneg_left (mul_nonneg hδ hs) (mul_pos hn hx)
        (mul_le_mul_of_nonneg_left hb hn.le)
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul hcos hsin hs (abs_nonneg _)) (mul_nonneg hn.le hx.le)

/-- Sine stays quantitatively positive on a fixed angular interior. -/
theorem node_sin_lower_on_interior (n : ℕ) (k : Fin n) (ε : ℝ)
    (hε : 0 ≤ ε) (hk₁ : ε ≤ angle n k) (hk₂ : angle n k ≤ Real.pi - ε) :
    2 / Real.pi * ε ≤ Real.sin (angle n k) :=
  sin_lower_of_margin hε hk₁ hk₂

end Erdos1151
