import Erdos1151.PrimitiveAsymptotics

noncomputable section
open Filter Topology

namespace Erdos1151

/-- The inclusion-exclusion error grows no faster than `n^(2/3)`. -/
theorem primitive_error_le_rpow (n : ℕ) (hn : 0 < n) :
    (2 : ℝ) ^ (oddPrimeFactors n).card ≤ (n : ℝ) ^ (2 / 3 : ℝ) := by
  have hcube : ((2 : ℝ) ^ (oddPrimeFactors n).card) ^ 3 ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast oddPrimeFactors_error_cube_le hn
  have hpow : ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (n : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0)
    (Real.rpow_nonneg (Nat.cast_nonneg n) (2 / 3 : ℝ))
  rwa [hpow]

/-- The elementary sieve error is eventually absorbed on every interval of
length at least `n^(3/4)`.  No prime-number asymptotics are used. -/
theorem primitive_error_eventually_absorbed :
    ∀ᶠ n : ℕ in atTop, 2 * (2 : ℝ) ^ (oddPrimeFactors n).card ≤
      primitiveDensity n * (n : ℝ) ^ (3 / 4 : ℝ) := by
  have hlittle :=
    (isLittleO_log_rpow_rpow_atTop (1 / 2 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 12)).comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hsmall := hlittle.bound (show 0 < densityConstant / 2 by
    exact div_pos densityConstant_pos (by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop 3] with n hn hn3
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤
      densityConstant / 2 * (n : ℝ) ^ (1 / 12 : ℝ) := by
    simpa only [Function.comp_apply, Real.norm_of_nonneg
      (Real.rpow_nonneg (Real.log_natCast_nonneg n) (1 / 2 : ℝ)),
      Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le (1 / 12 : ℝ))] using hn
  have hd := primitiveDensity_mul_sqrt_log_lower n hn3
  have hρ := primitiveDensity_pos n
  have hmul := mul_le_mul_of_nonneg_left hs hρ.le
  have htwo : 2 ≤ primitiveDensity n * (n : ℝ) ^ (1 / 12 : ℝ) := by
    have hcancel : densityConstant * 2 ≤ densityConstant *
        (primitiveDensity n * (n : ℝ) ^ (1 / 12 : ℝ)) := by
      nlinarith
    exact (mul_le_mul_iff_right₀ densityConstant_pos).mp hcancel
  have he := primitive_error_le_rpow n (by omega)
  calc
    2 * (2 : ℝ) ^ (oddPrimeFactors n).card ≤ 2 * (n : ℝ) ^ (2 / 3 : ℝ) := by
      gcongr
    _ ≤ (primitiveDensity n * (n : ℝ) ^ (1 / 12 : ℝ)) *
        (n : ℝ) ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hnpos.le _)
    _ = primitiveDensity n * (n : ℝ) ^ (3 / 4 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hnpos]
      norm_num

/-- Uniform lower density in all sufficiently long index intervals. -/
theorem primitive_count_eventually_half_density :
    ∀ᶠ n : ℕ in atTop, ∀ a M : ℕ,
      (n : ℝ) ^ (3 / 4 : ℝ) ≤ (M : ℝ) →
      (M : ℝ) * primitiveDensity n / 2 ≤
        (((Finset.Ico a (a + M)).filter
          (fun k => (2 * k + 1).Coprime n)).card : ℝ) := by
  filter_upwards [primitive_error_eventually_absorbed, eventually_ge_atTop 1]
    with n hn hn1
  intro a M hM
  have hρ := primitiveDensity_pos n
  have hmul := mul_le_mul_of_nonneg_left hM hρ.le
  have hcount := primitive_count_lower a M n (by omega)
  nlinarith

end Erdos1151
