import Erdos1151.ChebyshevShells
import Erdos1151.PrimitiveErrorAsymptotics

noncomputable section

open Filter Topology Finset
open scoped BigOperators

namespace Erdos1151

theorem angle_rev (n : ℕ) (k : Fin n) :
    angle n k.rev = Real.pi - angle n k := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt k.isLt)
  unfold angle
  rw [Fin.val_rev, Nat.cast_sub (by omega)]
  push_cast
  field_simp
  ring

theorem node_rev (n : ℕ) (k : Fin n) : node n k.rev = -node n k := by
  simp [node, angle_rev, Real.cos_pi_sub]

theorem primitive_rev (n : ℕ) (k : Fin n) (hk : Primitive n k) : Primitive n k.rev := by
  have hsum : (2 * k.rev.val + 1) + (2 * k.val + 1) = 2 * n := by
    rw [Fin.val_rev]
    omega
  let d := Nat.gcd (2 * k.rev.val + 1) n
  have hdA : d ∣ 2 * k.rev.val + 1 := Nat.gcd_dvd_left _ _
  have hdn : d ∣ n := Nat.gcd_dvd_right _ _
  have hdt : d ∣ 2 * n := dvd_mul_of_dvd_right hdn 2
  have hdB : d ∣ 2 * k.val + 1 := by
    have hh := Nat.dvd_sub hdt hdA
    rwa [← hsum, Nat.add_sub_cancel_left] at hh
  have hdg : d ∣ Nat.gcd (2 * k.val + 1) n := Nat.dvd_gcd hdB hdn
  change Nat.gcd (2 * k.val + 1) n = 1 at hk
  rw [hk] at hdg
  exact Nat.dvd_one.mp hdg

theorem primitive_rev_iff (n : ℕ) (k : Fin n) : Primitive n k.rev ↔ Primitive n k := by
  constructor
  · intro h
    simpa using primitive_rev n k.rev h
  · exact primitive_rev n k

theorem abs_coefficient_one (n : ℕ) (k : Fin n) :
    |coefficient n k 1| = Real.sin (angle n k) / ((n : ℝ) * (1 - node n k)) := by
  have hne : Real.cos 0 ≠ node n k := by
    simpa using (node_mem_Ioo n k).2.ne'
  simpa [abs_of_pos (sub_pos.mpr (node_mem_Ioo n k).2)] using
    abs_coefficient_formula n k 0 hne

theorem abs_coefficient_neg_one_rev (n : ℕ) (k : Fin n) :
    |coefficient n k.rev (-1)| = |coefficient n k 1| := by
  have hne : Real.cos Real.pi ≠ node n k.rev := by
    simpa using (node_mem_Ioo n k.rev).1.ne
  have hh := abs_coefficient_formula n k.rev Real.pi hne
  rw [abs_coefficient_one]
  have hh' : |coefficient n k.rev (-1)| =
      Real.sin (angle n k) / ((n : ℝ) * (-node n k + 1)) := by
    simpa [angle_rev, node_rev, Real.cos_nat_mul_pi,
      abs_of_pos (sub_pos.mpr (node_mem_Ioo n k).2), abs_of_neg (by
        linarith [(node_mem_Ioo n k).2] : -1 + node n k < 0)] using hh
  rw [hh']
  congr 1
  ring

/-- A stronger endpoint estimate uses the quadratic vanishing of `1-cos`. -/
theorem endpoint_coefficient_angle_lower (n : ℕ) (k : Fin n)
    (hhalf : angle n k ≤ Real.pi / 2) :
    4 / (Real.pi * (n : ℝ) * angle n k) ≤ |coefficient n k 1| := by
  have hφ := angle_pos n k
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  have hd : 0 < 1 - node n k := sub_pos.mpr (node_mem_Ioo n k).2
  have hsin : 2 / Real.pi * angle n k ≤ Real.sin (angle n k) :=
    sin_lower_of_margin hφ.le le_rfl (by linarith)
  have hcos : 1 - node n k ≤ angle n k ^ 2 / 2 := by
    have hh := Real.one_sub_sq_div_two_le_cos (x := angle n k)
    dsimp [node]
    linarith
  have hsm := mul_le_mul_of_nonneg_right hsin (mul_nonneg Real.pi_pos.le hφ.le)
  have heq : (2 / Real.pi * angle n k) * (Real.pi * angle n k) = 2 * angle n k ^ 2 := by
    field_simp
  have hcore : 4 * (1 - node n k) ≤ Real.sin (angle n k) * (Real.pi * angle n k) := by
    rw [heq] at hsm
    nlinarith
  rw [abs_coefficient_one]
  apply (div_le_div_iff₀ (by positivity : 0 < Real.pi * (n : ℝ) * angle n k)
    (mul_pos hnr hd)).2
  have hh := mul_le_mul_of_nonneg_left hcore hnr.le
  nlinarith

theorem endpoint_coefficient_lower (n m : ℕ) (hm : 1 ≤ m) (hmn : 2 * m ≤ n) :
    (4 / Real.pi ^ 2) / (m : ℝ) ≤
      |coefficient n ⟨m - 1, by omega⟩ 1| := by
  let k : Fin n := ⟨m - 1, by omega⟩
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hmc : (2 : ℝ) * m ≤ n := by exact_mod_cast hmn
  have hphi : angle n k ≤ Real.pi * m / n := by
    unfold angle k
    rw [Nat.cast_sub hm, Nat.cast_one]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) * n)).2
    have heq : (Real.pi * m / n) * (2 * n : ℝ) = 2 * Real.pi * m := by field_simp
    rw [heq]
    nlinarith [Real.pi_pos]
  have hhalf : angle n k ≤ Real.pi / 2 := by
    have hh : Real.pi * m / n ≤ Real.pi / 2 := by
      apply (div_le_iff₀ hnr).2
      nlinarith [Real.pi_pos]
    exact hphi.trans hh
  have hphin : (n : ℝ) * angle n k ≤ Real.pi * m := by
    have hh := (le_div_iff₀ hnr).mp hphi
    nlinarith
  have hden : Real.pi * (n : ℝ) * angle n k ≤ Real.pi ^ 2 * m := by
    nlinarith [mul_le_mul_of_nonneg_left hphin Real.pi_pos.le]
  calc
    (4 / Real.pi ^ 2) / (m : ℝ) = 4 / (Real.pi ^ 2 * m) := by ring
    _ ≤ 4 / (Real.pi * (n : ℝ) * angle n k) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity [angle_pos n k]) hden
    _ ≤ |coefficient n k 1| := endpoint_coefficient_angle_lower n k hhalf

theorem primitiveMass_neg_one_eq (n : ℕ) :
    primitiveMass n (fun k => coefficient n k (-1)) =
      primitiveMass n (fun k => coefficient n k 1) := by
  classical
  have himage : (primitiveNodes n).image Fin.rev = primitiveNodes n := by
    ext k
    constructor
    · intro hk
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
      exact (mem_primitiveNodes _).mpr (primitive_rev n j ((mem_primitiveNodes _).mp hj))
    · intro hk
      exact mem_image.mpr ⟨k.rev,
        (mem_primitiveNodes _).mpr (primitive_rev n k ((mem_primitiveNodes _).mp hk)), Fin.rev_rev _⟩
  calc
    primitiveMass n (fun k => coefficient n k (-1)) =
        ∑ k ∈ (primitiveNodes n).image Fin.rev, |coefficient n k (-1)| := by
      rw [himage]
      rfl
    _ = ∑ k ∈ primitiveNodes n, |coefficient n k.rev (-1)| :=
      sum_image Fin.rev_injective.injOn
    _ = primitiveMass n (fun k => coefficient n k 1) := by
      simp only [abs_coefficient_neg_one_rev, primitiveMass]

/-- The reciprocal estimate embeds into the actual primitive coefficient mass
at the endpoint, using the injective correspondence `m ↦ m-1`. -/
theorem primitiveMass_one_ge_reciprocal (n M B : ℕ) (hn : 0 < n)
    (hM : 1 ≤ M) (hB : 2 * B ≤ n) :
    (4 / Real.pi ^ 2) * goodReciprocalSum (fun m => (2 * (m - 1) + 1).Coprime n) M B ≤
      primitiveMass n (fun k => coefficient n k 1) := by
  classical
  let S := (Ico M B).filter fun m => (2 * (m - 1) + 1).Coprime n
  let F : ℕ → Fin n := fun m => ⟨(m - 1) % n, Nat.mod_lt _ hn⟩
  have hmem : ∀ m ∈ S, M ≤ m ∧ m < B := by
    intro m hm
    exact mem_Ico.mp (mem_filter.mp hm).1
  have hF : ∀ m ∈ S, (F m).val = m - 1 := by
    intro m hm
    exact Nat.mod_eq_of_lt (by have := hmem m hm; omega)
  have hFinj : Set.InjOn F S := by
    intro a ha b hb hab
    have hv := congrArg Fin.val hab
    rw [hF a ha, hF b hb] at hv
    have := hmem a ha
    have := hmem b hb
    omega
  have hsub : S.image F ⊆ primitiveNodes n := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hk
    rw [mem_primitiveNodes, Primitive, hF m hm]
    exact (mem_filter.mp hm).2
  have hterm : ∀ m ∈ S, (4 / Real.pi ^ 2) / (m : ℝ) ≤ |coefficient n (F m) 1| := by
    intro m hm
    have hm1 := hM.trans (hmem m hm).1
    have hmn : 2 * m ≤ n := by have := hmem m hm; omega
    have heq : F m = ⟨m - 1, by omega⟩ := Fin.ext (hF m hm)
    rw [heq]
    exact endpoint_coefficient_lower n m hm1 hmn
  calc
    _ = ∑ m ∈ S, (4 / Real.pi ^ 2) / (m : ℝ) := by
      simp [goodReciprocalSum, S, mul_sum, div_eq_mul_inv]
    _ ≤ ∑ m ∈ S, |coefficient n (F m) 1| := sum_le_sum hterm
    _ = ∑ k ∈ S.image F, |coefficient n k 1| := by rw [sum_image hFinj]
    _ ≤ primitiveMass n (fun k => coefficient n k 1) := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      exact fun k _ _ => abs_nonneg _

@[simp] theorem shellIndex_zero (n m : ℕ) : shellIndex 0 n m = m - 1 := by
  norm_num [shellIndex]

theorem endpoint_count_lower (n L : ℕ) (hn : 0 < n) (hL : 1 ≤ L) :
    primitiveDensity n * (L : ℝ) - (2 : ℝ) ^ (oddPrimeFactors n).card ≤
      (((Ico L (2 * L)).filter fun m => (2 * (m - 1) + 1).Coprime n).card : ℝ) := by
  simpa only [shellIndex_zero] using shell_count_lower 0 n L hn hL

theorem primitiveMass_one_log_lower (n : ℕ) (hn : 1 ≤ n)
    (hcn : 2 ≤ (1 / 4 : ℝ) * (n : ℝ))
    (hlarge : 8 * (3 * Real.log 2 - Real.log (1 / 4 : ℝ)) ≤ Real.log (n : ℝ))
    (herr : 2 * (2 : ℝ) ^ (oddPrimeFactors n).card ≤
      primitiveDensity n * (n : ℝ) ^ (3 / 4 : ℝ)) :
    (4 / Real.pi ^ 2) * (primitiveDensity n * Real.log (n : ℝ) / (32 * Real.log 2)) ≤
      primitiveMass n (fun k => coefficient n k 1) := by
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hcut : 1 ≤ Nat.ceil ((n : ℝ) ^ (3 / 4 : ℝ)) :=
    Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnr _)
  have hh := reciprocal_three_quarter_lower_of_error
    (fun m => (2 * (m - 1) + 1).Coprime n) n hn
    (by norm_num : (0 : ℝ) < 1 / 4) (primitiveDensity_pos n).le hcn hlarge
    (fun L hL => endpoint_count_lower n L hn0 (hcut.trans hL)) herr
  have hB : 2 * Nat.floor ((1 / 4 : ℝ) * (n : ℝ)) ≤ n := by
    have hf := Nat.floor_le (by positivity : 0 ≤ (1 / 4 : ℝ) * (n : ℝ))
    have hbr : (2 : ℝ) * (Nat.floor ((1 / 4 : ℝ) * (n : ℝ)) : ℝ) ≤ (n : ℝ) := by
      linarith
    exact_mod_cast hbr
  have hm := primitiveMass_one_ge_reciprocal n
    (Nat.ceil ((n : ℝ) ^ (3 / 4 : ℝ))) (Nat.floor ((1 / 4 : ℝ) * (n : ℝ))) hn0 hcut hB
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans hm

def endpointMassConstant : ℝ :=
  (4 / Real.pi ^ 2) * densityConstant / (32 * Real.log 2)

theorem endpointMassConstant_pos : 0 < endpointMassConstant := by
  unfold endpointMassConstant
  have hd := densityConstant_pos
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem primitiveMass_one_sqrt_log_lower (n : ℕ) (hn : 3 ≤ n)
    (hcn : 2 ≤ (1 / 4 : ℝ) * (n : ℝ))
    (hlarge : 8 * (3 * Real.log 2 - Real.log (1 / 4 : ℝ)) ≤ Real.log (n : ℝ))
    (herr : 2 * (2 : ℝ) ^ (oddPrimeFactors n).card ≤
      primitiveDensity n * (n : ℝ) ^ (3 / 4 : ℝ)) :
    endpointMassConstant * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤
      primitiveMass n (fun k => coefficient n k 1) := by
  have hd := primitiveDensity_log_lower n hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hd (by positivity : (0 : ℝ) ≤ 32 * Real.log 2))
    (by positivity : (0 : ℝ) ≤ 4 / Real.pi ^ 2)
  have hm := primitiveMass_one_log_lower n (by omega) hcn hlarge herr
  calc
    _ = (4 / Real.pi ^ 2) *
        (densityConstant * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) / (32 * Real.log 2)) := by
      unfold endpointMassConstant
      ring
    _ ≤ _ := h.trans hm

/-- The complete endpoint lower bound, with all arithmetic estimates discharged. -/
theorem eventually_primitiveMass_one_lower :
    ∀ᶠ n : ℕ in atTop,
      endpointMassConstant * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤
        primitiveMass n (fun k => coefficient n k 1) := by
  have hlarge : ∀ᶠ n : ℕ in atTop,
      8 * (3 * Real.log 2 - Real.log (1 / 4 : ℝ)) ≤ Real.log (n : ℝ) :=
    log_nat_tendsto.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop 8, hlarge, primitive_error_eventually_absorbed]
    with n hn hl he
  have hnr : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact primitiveMass_one_sqrt_log_lower n (by omega) (by linarith) hl he

theorem eventually_primitiveMass_neg_one_lower :
    ∀ᶠ n : ℕ in atTop,
      endpointMassConstant * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤
        primitiveMass n (fun k => coefficient n k (-1)) := by
  simpa only [primitiveMass_neg_one_eq] using eventually_primitiveMass_one_lower

theorem exists_endpoint_mass_lower (x : ℝ) (hx : x = -1 ∨ x = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤
        primitiveMass n (fun k => coefficient n k x) := by
  refine ⟨endpointMassConstant, endpointMassConstant_pos, ?_⟩
  rcases hx with rfl | rfl
  · exact eventually_primitiveMass_neg_one_lower
  · exact eventually_primitiveMass_one_lower

end Erdos1151
