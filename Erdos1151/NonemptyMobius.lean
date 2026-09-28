import Mathlib

/-!
Actual arithmetic of the finite algebraic spike in Chojecki's construction.
The stronger tail estimate below uses the injection d ↦ u/d on divisors d>R,
rather than a square-root bound for the total divisor count.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Erdos1151.NonemptyAssembly

def oddCharacter (s : ℕ) : ℝ := (-1) ^ ((s - 1) / 2)

@[simp] theorem oddCharacter_one : oddCharacter 1 = 1 := by simp [oddCharacter]

@[simp] theorem abs_oddCharacter (s : ℕ) : |oddCharacter s| = 1 := by
  simp [oddCharacter, abs_pow]

theorem oddCharacter_mul {s t : ℕ} (hs : Odd s) (ht : Odd t) :
    oddCharacter (s * t) = oddCharacter s * oddCharacter t := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  have hs' : (s - 1) / 2 = a := by omega
  have ht' : (t - 1) / 2 = b := by omega
  have hst : s * t = 2 * (2 * a * b + a + b) + 1 := by rw [ha, hb]; ring
  have hst' : (s * t - 1) / 2 = 2 * a * b + a + b := by rw [hst]; omega
  simp only [oddCharacter, hs', ht', hst', pow_add]
  have hpow : (-1 : ℝ) ^ (2 * a * b) = 1 := by
    rw [mul_assoc, pow_mul, neg_one_sq, one_pow]
  rw [hpow, one_mul]

theorem moebius_divisor_sum (u : ℕ) :
    (∑ s ∈ u.divisors, (μ s : ℝ)) = if u = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f u)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact_mod_cast h

def truncatedMoebiusSum (R u : ℕ) : ℝ :=
  ∑ s ∈ u.divisors.filter (fun s => s ≤ R), (μ s : ℝ)

theorem truncatedMoebiusSum_of_le {R u : ℕ} (huR : u ≤ R) :
    truncatedMoebiusSum R u = if u = 1 then 1 else 0 := by
  have hfilter : u.divisors.filter (fun s => s ≤ R) = u.divisors := by
    apply Finset.filter_eq_self.mpr
    intro s hs
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hs).2)
      (Nat.mem_divisors.mp hs).1).trans huR
  rw [truncatedMoebiusSum, hfilter, moebius_divisor_sum]

theorem truncatedMoebiusSum_tail {R u : ℕ} (hu : u ≠ 1) :
    truncatedMoebiusSum R u = -∑ s ∈ u.divisors.filter (fun s => R < s), (μ s : ℝ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := u.divisors) (p := fun s => s ≤ R) (f := fun s => (μ s : ℝ))
  rw [moebius_divisor_sum, if_neg hu] at hsplit
  simpa only [truncatedMoebiusSum, not_le, eq_neg_iff_add_eq_zero] using hsplit

theorem card_large_divisors_le (R u : ℕ) :
    (u.divisors.filter (fun s => R < s)).card ≤ u / (R + 1) := by
  have hc : (u.divisors.filter (fun s => R < s)).card ≤
      (Finset.Icc 1 (u / (R + 1))).card := by
    apply Finset.card_le_card_of_injOn (fun s => u / s)
    · intro s hs
      obtain ⟨hsd, hRs⟩ := Finset.mem_filter.mp hs
      obtain ⟨hsu, hu⟩ := Nat.mem_divisors.mp hsd
      apply Finset.mem_Icc.mpr
      exact ⟨Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hu) hsu) (by omega),
        Nat.div_le_div_left (by omega) (by omega)⟩
    · intro s hs t ht heq
      have hsd := Nat.mem_divisors.mp (Finset.mem_filter.mp hs).1
      have htd := Nat.mem_divisors.mp (Finset.mem_filter.mp ht).1
      have h := congrArg (fun k => u / k) heq
      simpa [Nat.div_div_self hsd.1 hsd.2, Nat.div_div_self htd.1 htd.2] using h
  simpa using hc

theorem abs_truncatedMoebiusSum_le {R u : ℕ} (hu : u ≠ 1) :
    |truncatedMoebiusSum R u| ≤ (u : ℝ) / (R + 1) := by
  rw [truncatedMoebiusSum_tail hu, abs_neg]
  calc
    |∑ s ∈ u.divisors.filter (fun s => R < s), (μ s : ℝ)|
        ≤ ∑ s ∈ u.divisors.filter (fun s => R < s), |(μ s : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ u.divisors.filter (fun s => R < s), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := s))
    _ = ((u.divisors.filter (fun s => R < s)).card : ℝ) := by simp
    _ ≤ ((u / (R + 1) : ℕ) : ℝ) := by exact_mod_cast card_large_divisors_le R u
    _ ≤ (u : ℝ) / (R + 1) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < R + 1)).mpr
      have hn := Nat.div_mul_le_self u (R + 1)
      exact_mod_cast hn

/-- The primitive-layer amplitude, with the cosine factor retained. -/
def layerAmplitude (n s : ℕ) (θ : ℝ) : ℝ :=
  (μ s : ℝ) * oddCharacter s * Real.cos ((n * s : ℕ) * θ) /
    ((s : ℝ) * Real.cos ((n : ℝ) * θ))

/-- Transfer of a primitive atom from layer ns into row nu. -/
def layerTransfer (n u s : ℕ) (θ : ℝ) : ℝ :=
  (s : ℝ) / u * oddCharacter (u / s) *
    Real.cos ((n * u : ℕ) * θ) / Real.cos ((n * s : ℕ) * θ)

theorem layer_product {n u s : ℕ} {θ : ℝ}
    (hu : Odd u) (hsu : s ∣ u)
    (hcos : Real.cos ((n * s : ℕ) * θ) ≠ 0) :
    layerTransfer n u s θ * layerAmplitude n s θ =
      oddCharacter u * Real.cos ((n * u : ℕ) * θ) /
        ((u : ℝ) * Real.cos ((n : ℝ) * θ)) * (μ s : ℝ) := by
  have hs : 0 < s := Nat.pos_of_dvd_of_pos hsu hu.pos
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hχ : oddCharacter (u / s) * oddCharacter s = oddCharacter u := by
    rw [← oddCharacter_mul (hu.of_dvd_nat (Nat.div_dvd_of_dvd hsu))
      (hu.of_dvd_nat hsu), Nat.div_mul_cancel hsu]
  unfold layerTransfer layerAmplitude
  by_cases hbase : Real.cos ((n : ℝ) * θ) = 0
  · simp [hbase]
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu.pos.ne'
  have hcos' : Real.cos (θ * (n * s : ℕ)) ≠ 0 := by simpa [mul_comm] using hcos
  have hbase' : Real.cos (θ * (n : ℝ)) ≠ 0 := by simpa [mul_comm] using hbase
  calc
    _ = (oddCharacter (u / s) * oddCharacter s) *
        (Real.cos ((n * u : ℕ) * θ) /
        ((u : ℝ) * Real.cos ((n : ℝ) * θ))) * (μ s : ℝ) := by
      field_simp [hsR, huR, hcos, hbase, hcos', hbase']
    _ = _ := by rw [hχ]; ring

theorem truncated_layer_response {n u R : ℕ} {θ : ℝ} (hu : Odd u)
    (hcos : ∀ s ∈ u.divisors.filter (fun s => s ≤ R),
      Real.cos ((n * s : ℕ) * θ) ≠ 0) :
    (∑ s ∈ u.divisors.filter (fun s => s ≤ R),
      layerTransfer n u s θ * layerAmplitude n s θ) =
      oddCharacter u * Real.cos ((n * u : ℕ) * θ) /
        ((u : ℝ) * Real.cos ((n : ℝ) * θ)) * truncatedMoebiusSum R u := by
  unfold truncatedMoebiusSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact layer_product hu (Nat.mem_divisors.mp (Finset.mem_filter.mp hs).1).1 (hcos s hs)

theorem finite_layer_delta {n u R : ℕ} {θ : ℝ} (hu : Odd u) (huR : u ≤ R)
    (hbase : Real.cos ((n : ℝ) * θ) ≠ 0)
    (hcos : ∀ s ∈ u.divisors.filter (fun s => s ≤ R),
      Real.cos ((n * s : ℕ) * θ) ≠ 0) :
    (∑ s ∈ u.divisors.filter (fun s => s ≤ R),
      layerTransfer n u s θ * layerAmplitude n s θ) = if u = 1 then 1 else 0 := by
  rw [truncated_layer_response hu hcos, truncatedMoebiusSum_of_le huR]
  by_cases hu1 : u = 1
  · subst u
    simp [hbase]
  · simp [hu1]

theorem uniform_tail_layer_bound {n u R : ℕ} {θ κ : ℝ}
    (hu : Odd u) (hu1 : u ≠ 1) (hκ : 0 < κ)
    (hbase : κ ≤ |Real.cos ((n : ℝ) * θ)|)
    (hcos : ∀ s ∈ u.divisors.filter (fun s => s ≤ R),
      Real.cos ((n * s : ℕ) * θ) ≠ 0) :
    |∑ s ∈ u.divisors.filter (fun s => s ≤ R),
      layerTransfer n u s θ * layerAmplitude n s θ| ≤ 1 / (κ * (R + 1)) := by
  have huR : 0 < (u : ℝ) := by exact_mod_cast hu.pos
  have hbasepos : 0 < |Real.cos ((n : ℝ) * θ)| := hκ.trans_le hbase
  rw [truncated_layer_response hu hcos, abs_mul, abs_div, abs_mul, abs_mul,
    abs_oddCharacter, one_mul, abs_of_pos huR]
  calc
    _ ≤ (1 / ((u : ℝ) * κ)) * ((u : ℝ) / (R + 1)) := by
      apply mul_le_mul _ (abs_truncatedMoebiusSum_le hu1) (abs_nonneg _)
        (by positivity)
      apply div_le_div₀ (by norm_num) (Real.abs_cos_le_one _)
        (by positivity) (mul_le_mul_of_nonneg_left hbase huR.le)
    _ = _ := by field_simp

theorem layerAmplitude_abs_bound {n s : ℕ} {θ κ : ℝ} (hs : 0 < s)
    (hκ : 0 < κ) (hbase : κ ≤ |Real.cos ((n : ℝ) * θ)|) :
    |layerAmplitude n s θ| ≤ 1 / ((s : ℝ) * κ) := by
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hbasepos : 0 < |Real.cos ((n : ℝ) * θ)| := hκ.trans_le hbase
  rw [layerAmplitude, abs_div, abs_mul, abs_mul, abs_mul, abs_oddCharacter,
    mul_one, abs_of_pos hsR]
  apply div_le_div₀ (by norm_num) _ (by positivity)
    (mul_le_mul_of_nonneg_left hbase hsR.le)
  calc
    |(μ s : ℝ)| * |Real.cos ((n * s : ℕ) * θ)| ≤ 1 * 1 :=
      mul_le_mul (by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := s)))
        (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

end Erdos1151.NonemptyAssembly
