import Erdos1151.PrimitiveCounting
import Erdos1151.Weights

noncomputable section
open Filter Topology

namespace Erdos1151

theorem oddPrimeFactors_log_bound (n : ℕ) (hn : 0 < n) :
    ((oddPrimeFactors n).card : ℝ) * Real.log 3 ≤ Real.log (n : ℝ) := by
  have hp : (3 : ℝ) ^ (oddPrimeFactors n).card ≤ (n : ℝ) := by
    exact_mod_cast oddPrimeFactors_three_pow_le hn
  simpa only [Real.log_pow] using Real.log_le_log (by positivity) hp

theorem primitiveDensity_log_sq_lower (n : ℕ) (hn : 3 ≤ n) :
    Real.log 3 / 3 ≤ Real.log (n : ℝ) * primitiveDensity n ^ 2 := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogn : Real.log 3 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hω := oddPrimeFactors_log_bound n (by omega)
  have hρ := primitiveDensity_sq_lower n
  have hρ0 := sq_nonneg (primitiveDensity n)
  have h1 := mul_le_mul_of_nonneg_right (show
      (2 * ((oddPrimeFactors n).card : ℝ) + 1) * Real.log 3 ≤
        3 * Real.log (n : ℝ) by nlinarith) hρ0
  have h2 := mul_le_mul_of_nonneg_left hρ hlog3.le
  nlinarith

def densityConstant : ℝ := (Real.log 3 / 3) ^ (1 / 2 : ℝ)

theorem densityConstant_pos : 0 < densityConstant := by
  unfold densityConstant
  exact Real.rpow_pos_of_pos (div_pos (Real.log_pos (by norm_num)) (by norm_num)) _

theorem primitiveDensity_mul_sqrt_log_lower (n : ℕ) (hn : 3 ≤ n) :
    densityConstant ≤ primitiveDensity n * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) := by
  have hr := primitiveDensity_pos n
  have hl := Real.log_natCast_nonneg n
  have hs := Real.rpow_nonneg hl (1 / 2 : ℝ)
  have hd := densityConstant_pos
  have hd2 : densityConstant ^ 2 = Real.log 3 / 3 := by
    unfold densityConstant
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hs2 : ((Real.log (n : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 = Real.log (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl]
    norm_num
  have heq : (primitiveDensity n * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 =
      primitiveDensity n ^ 2 * Real.log (n : ℝ) := by rw [mul_pow, hs2]
  have hbound := primitiveDensity_log_sq_lower n hn
  have hp := mul_nonneg hr.le hs
  nlinarith

theorem primitiveDensity_log_lower (n : ℕ) (hn : 3 ≤ n) :
    densityConstant * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤
      primitiveDensity n * Real.log (n : ℝ) := by
  have hl := Real.log_natCast_nonneg n
  have h := mul_le_mul_of_nonneg_right (primitiveDensity_mul_sqrt_log_lower n hn)
    (Real.rpow_nonneg hl (1 / 2 : ℝ))
  have heq : (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) *
      (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) = Real.log (n : ℝ) := by
    rw [← Real.rpow_add (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))]
    norm_num
  simpa only [mul_assoc, heq] using h

end Erdos1151
