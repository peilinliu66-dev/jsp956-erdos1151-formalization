import Mathlib

noncomputable section
open Filter Topology

namespace Erdos1151

/-- The slower decay compatible with the elementary primitive-mass bound. -/
def amplitude (n : ℕ) : ℝ := (Real.log (n : ℝ)) ^ (-(1 / 4 : ℝ))

theorem amplitude_nonneg (n : ℕ) : 0 ≤ amplitude n :=
  Real.rpow_nonneg (Real.log_natCast_nonneg n) _

theorem log_nat_tendsto : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem amplitude_tendsto_zero : Tendsto amplitude atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp log_nat_tendsto

theorem amplitude_mass_identity (n : ℕ) (hn : 2 ≤ n) :
    amplitude n * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) =
      (Real.log (n : ℝ)) ^ (1 / 4 : ℝ) := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [amplitude, ← Real.rpow_add hlog]
  norm_num

theorem weighted_mass_tendsto {S : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hS : ∀ᶠ (n : ℕ) in atTop, c * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤ S n) :
    Tendsto (fun n => amplitude n * S n) atTop atTop := by
  have hlow : Tendsto (fun n : ℕ => c * (Real.log (n : ℝ)) ^ (1 / 4 : ℝ))
      atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      log_nat_tendsto).const_mul_atTop hc
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [hS, eventually_ge_atTop 2] with n hn hn2
  calc
    c * (Real.log (n : ℝ)) ^ (1 / 4 : ℝ) =
        amplitude n * (c * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ)) := by
          rw [mul_left_comm, amplitude_mass_identity n hn2]
    _ ≤ amplitude n * S n := mul_le_mul_of_nonneg_left hn (amplitude_nonneg n)

theorem amplitude_square_contraction (n m : ℕ) (hn : 2 ≤ n) (hnm : n ^ 2 ≤ m) :
    amplitude m ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) * amplitude n := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hn1
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hpow : (n : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast hnm
  have hlogs : 2 * Real.log (n : ℝ) ≤ Real.log (m : ℝ) := by
    simpa [Real.log_pow] using Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) ^ 2) hpow
  unfold amplitude
  calc
    (Real.log (m : ℝ)) ^ (-(1 / 4 : ℝ)) ≤
        (2 * Real.log (n : ℝ)) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlogs (by norm_num)
    _ = _ := Real.mul_rpow (by norm_num) hlog.le

theorem contraction_factor_bounds :
    0 < (2 : ℝ) ^ (-(1 / 4 : ℝ)) ∧ (2 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 := by
  constructor
  · positivity
  · exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem amplitude_antitone_from_two {n m : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m) :
    amplitude m ≤ amplitude n := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  exact Real.rpow_le_rpow_of_nonpos (Real.log_pos hn1)
    (Real.log_le_log (by linarith) (by exact_mod_cast hnm)) (by norm_num)

theorem shifted_amplitude_antitone : Antitone (fun n => amplitude (n + 2)) := by
  intro n m hnm
  exact amplitude_antitone_from_two (by omega) (by omega)

theorem shifted_amplitude_tendsto_zero :
    Tendsto (fun n => amplitude (n + 2)) atTop (𝓝 0) :=
  amplitude_tendsto_zero.comp (tendsto_add_atTop_nat 2)

end Erdos1151
