import Erdos1151.ChebyshevWeights
import Erdos1151.NonemptyMobius

/-! Primitive-node arithmetic and actual coefficient transfer across rows. -/

noncomputable section

namespace Erdos1151.NonemptyAssembly

theorem primitive_row_divides {d n : ℕ} (k : Fin d) (j : Fin n)
    (hk : Primitive d k) (heq : node d k = node n j) : d ∣ n := by
  have hcross := (node_eq_iff_cross_mul k j).mp heq
  have hd : d ∣ (2 * k.val + 1) * n := by rw [hcross]; exact dvd_mul_left _ _
  exact hk.symm.dvd_of_dvd_mul_left hd

theorem primitive_index_transfer {d n : ℕ} (k : Fin d) (j : Fin n)
    (hk : Primitive d k) (heq : node d k = node n j) :
    (2 * k.val + 1) * (n / d) = 2 * j.val + 1 := by
  have hd : d ∣ n := primitive_row_divides k j hk heq
  have hcross := (node_eq_iff_cross_mul k j).mp heq
  have hdpos : 0 < d := Nat.zero_lt_of_lt k.isLt
  apply Nat.eq_of_mul_eq_mul_right hdpos
  calc
    ((2 * k.val + 1) * (n / d)) * d = (2 * k.val + 1) * n := by
      rw [mul_assoc, Nat.div_mul_cancel hd]
    _ = (2 * j.val + 1) * d := hcross

theorem primitive_row_quotient_odd {d n : ℕ} (k : Fin d) (j : Fin n)
    (hk : Primitive d k) (heq : node d k = node n j) : Odd (n / d) := by
  have hcross := primitive_index_transfer k j hk heq
  have hodd : Odd (2 * j.val + 1) := ⟨j.val, by omega⟩
  apply hodd.of_dvd_nat
  rw [← hcross]
  exact dvd_mul_left _ _

theorem primitive_order_unique {d n : ℕ} (k : Fin d) (j : Fin n)
    (hk : Primitive d k) (hj : Primitive n j) (heq : node d k = node n j) : d = n :=
  Nat.dvd_antisymm (primitive_row_divides k j hk heq)
    (primitive_row_divides j k hj heq.symm)

theorem primitive_sign_transfer {d n : ℕ} (k : Fin d) (j : Fin n)
    (hk : Primitive d k) (heq : node d k = node n j) :
    (-1 : ℝ) ^ j.val = oddCharacter (n / d) * (-1 : ℝ) ^ k.val := by
  have hcross := primitive_index_transfer k j hk heq
  have hodd := primitive_row_quotient_odd k j hk heq
  obtain ⟨b, hb⟩ := hodd
  have hi : j.val = 2 * k.val * b + k.val + b := by
    rw [hb] at hcross
    nlinarith
  have hquot : (n / d - 1) / 2 = b := by omega
  rw [hi, oddCharacter, hquot, pow_add, pow_add]
  have hp : (-1 : ℝ) ^ (2 * k.val * b) = 1 := by
    rw [mul_assoc, pow_mul, neg_one_sq, one_pow]
  rw [hp, one_mul, mul_comm]

theorem primitive_coefficient_transfer {d n : ℕ} (k : Fin d) (j : Fin n)
    (θ : ℝ) (hk : Primitive d k) (heq : node d k = node n j)
    (hpoint : Real.cos θ ≠ node d k)
    (hcos : Real.cos ((d : ℝ) * θ) ≠ 0) :
    coefficient n j (Real.cos θ) =
      ((d : ℝ) / n * oddCharacter (n / d) *
        Real.cos ((n : ℝ) * θ) / Real.cos ((d : ℝ) * θ)) *
      coefficient d k (Real.cos θ) := by
  have hang : angle d k = angle n j :=
    Real.strictAntiOn_cos.injOn (angle_mem_Icc d k) (angle_mem_Icc n j) heq
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt j.isLt)
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt k.isLt)
  have hx : Real.cos θ - node d k ≠ 0 := sub_ne_zero.mpr hpoint
  have hsign : (-1 : ℝ) ^ k.val ≠ 0 := by positivity
  have hχ : oddCharacter (n / d) ≠ 0 := by
    intro h
    have h' := abs_oddCharacter (n / d)
    rw [h, abs_zero] at h'
    norm_num at h'
  have hχsq : oddCharacter (n / d) ^ 2 = 1 := by
    unfold oddCharacter
    rw [← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq, one_pow]
  rw [coefficient_formula n j θ (by simpa [← heq] using hpoint),
    coefficient_formula d k θ hpoint, ← heq, ← hang,
    primitive_sign_transfer k j hk heq]
  have hcos' : Real.cos (θ * (d : ℝ)) ≠ 0 := by simpa [mul_comm] using hcos
  field_simp [hn, hd, hx, hsign, hχ, hcos, hcos']
  rw [hχsq, mul_one]

/-- The same node in an odd multiple of its original row. -/
def oddLiftIndex {d : ℕ} (s : ℕ) (hs : Odd s) (k : Fin d) : Fin (d * s) :=
  ⟨k.val * s + (s - 1) / 2, by
    obtain ⟨b, hb⟩ := hs
    have hhalf : (s - 1) / 2 = b := by omega
    rw [hhalf]
    have hk : k.val + 1 ≤ d := k.isLt
    have hb0 : 0 ≤ b := Nat.zero_le b
    nlinarith⟩

theorem node_oddLiftIndex {d : ℕ} (s : ℕ) (hs : Odd s) (k : Fin d) :
    node d k = node (d * s) (oddLiftIndex s hs k) := by
  apply (node_eq_iff_cross_mul k _).mpr
  change (2 * k.val + 1) * (d * s) =
    (2 * (k.val * s + (s - 1) / 2) + 1) * d
  obtain ⟨b, hb⟩ := hs
  have hhalf : (s - 1) / 2 = b := by omega
  rw [hhalf, hb]
  ring

theorem oddLiftIndex_injective {d : ℕ} (s : ℕ) (hs : Odd s) :
    Function.Injective (oddLiftIndex (d := d) s hs) := by
  intro k j h
  apply node_injective d
  rw [node_oddLiftIndex s hs k, node_oddLiftIndex s hs j, h]

theorem primitive_occurs_iff {d n : ℕ} (k : Fin d) (hk : Primitive d k) :
    (∃ j : Fin n, node d k = node n j) ↔ ∃ s, Odd s ∧ n = d * s := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨n / d, primitive_row_quotient_odd k j hk hj,
      (Nat.mul_div_cancel' (primitive_row_divides k j hk hj)).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨oddLiftIndex s hs k, node_oddLiftIndex s hs k⟩

theorem primitive_actual_layer_transfer {n u s : ℕ} (hn : 0 < n)
    (k : Fin (n * s)) (j : Fin (n * u)) (θ : ℝ)
    (hk : Primitive (n * s) k) (heq : node (n * s) k = node (n * u) j)
    (hpoint : Real.cos θ ≠ node (n * s) k)
    (hcos : Real.cos (((n * s : ℕ) : ℝ) * θ) ≠ 0) :
    coefficient (n * u) j (Real.cos θ) =
      layerTransfer n u s θ * coefficient (n * s) k (Real.cos θ) := by
  rw [primitive_coefficient_transfer k j θ hk heq hpoint hcos]
  congr 1
  unfold layerTransfer
  rw [Nat.mul_div_mul_left _ _ hn]
  push_cast
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [mul_div_mul_left _ _ hnR]

end Erdos1151.NonemptyAssembly
