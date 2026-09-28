import Erdos1151.ChebyshevShells
import Erdos1151.PrimitiveAsymptotics
import Erdos1151.PrimitiveErrorAsymptotics

noncomputable section

open Filter Topology

namespace Erdos1151

def interiorMassConstant (θ η : ℝ) : ℝ :=
  (η * (2 / Real.pi * min θ ((Real.pi - θ) / 2)) / Real.pi) *
    densityConstant / (32 * Real.log 2)

theorem interiorMassConstant_pos {θ η : ℝ}
    (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) (hη : 0 < η) :
    0 < interiorMassConstant θ η := by
  unfold interiorMassConstant
  have hd := densityConstant_pos
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem primitiveMass_interior_sqrt_log_lower (θ η : ℝ) (n : ℕ)
    (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) (hn : 3 ≤ n) (hη : 0 ≤ η)
    (hcos : η ≤ |Real.cos ((n : ℝ) * θ)|)
    (hcn : 2 ≤ shellFraction θ * (n : ℝ))
    (hlarge : 8 * (3 * Real.log 2 - Real.log (shellFraction θ)) ≤ Real.log (n : ℝ))
    (herr : 2 * (2 : ℝ) ^ (oddPrimeFactors n).card ≤
      primitiveDensity n * (n : ℝ) ^ (3 / 4 : ℝ)) :
    interiorMassConstant θ η * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤
      primitiveMass n (fun k => coefficient n k (Real.cos θ)) := by
  have hd := primitiveDensity_log_lower n hn
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hnonneg : 0 ≤ η * (2 / Real.pi * min θ ((Real.pi - θ) / 2)) / Real.pi := by
    positivity
  have h := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hd (by positivity : (0 : ℝ) ≤ 32 * Real.log 2)) hnonneg
  have hf := primitiveMass_interior_log_lower θ η n hθ₀ hθπ (by omega)
    hη hcos hcn hlarge herr
  calc
    _ = (η * (2 / Real.pi * min θ ((Real.pi - θ) / 2)) / Real.pi) *
        (densityConstant * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) / (32 * Real.log 2)) := by
      unfold interiorMassConstant
      ring
    _ ≤ _ := h.trans hf

theorem eventually_primitiveMass_interior_lower_of_error
    (θ η : ℝ) (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) (hη : 0 ≤ η)
    (hcos : ∀ n : ℕ, η ≤ |Real.cos ((n : ℝ) * θ)|)
    (herr : ∀ᶠ n : ℕ in atTop, 2 * (2 : ℝ) ^ (oddPrimeFactors n).card ≤
      primitiveDensity n * (n : ℝ) ^ (3 / 4 : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      interiorMassConstant θ η * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤
        primitiveMass n (fun k => coefficient n k (Real.cos θ)) := by
  have hc := shellFraction_pos hθπ
  have hcn : ∀ᶠ n : ℕ in atTop, 2 ≤ shellFraction θ * (n : ℝ) := by
    have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (eventually_ge_atTop (2 / shellFraction θ))] with n hn
    have heq : shellFraction θ * (2 / shellFraction θ) = 2 := by field_simp
    have hh := mul_le_mul_of_nonneg_left hn hc.le
    rwa [heq] at hh
  have hlarge : ∀ᶠ n : ℕ in atTop,
      8 * (3 * Real.log 2 - Real.log (shellFraction θ)) ≤ Real.log (n : ℝ) :=
    log_nat_tendsto.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop 3, hcn, hlarge, herr] with n hn hc hl he
  exact primitiveMass_interior_sqrt_log_lower θ η n hθ₀ hθπ hn hη (hcos n) hc hl he

/-- The full interior mass estimate, with no sieve or asymptotic hypothesis left. -/
theorem eventually_primitiveMass_interior_lower
    (θ η : ℝ) (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) (hη : 0 ≤ η)
    (hcos : ∀ n : ℕ, η ≤ |Real.cos ((n : ℝ) * θ)|) :
    ∀ᶠ n : ℕ in atTop,
      interiorMassConstant θ η * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤
        primitiveMass n (fun k => coefficient n k (Real.cos θ)) :=
  eventually_primitiveMass_interior_lower_of_error θ η hθ₀ hθπ hη hcos
    primitive_error_eventually_absorbed

/-- The mass certificate for every interior angle admitting a uniform cosine bound. -/
theorem exists_interior_mass_lower (θ : ℝ) (hθ₀ : 0 < θ) (hθπ : θ < Real.pi)
    (hcos : ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, η ≤ |Real.cos ((n : ℝ) * θ)|) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤
        primitiveMass n (fun k => coefficient n k (Real.cos θ)) := by
  obtain ⟨η, hη, hbound⟩ := hcos
  exact ⟨interiorMassConstant θ η, interiorMassConstant_pos hθ₀ hθπ hη,
    eventually_primitiveMass_interior_lower θ η hθ₀ hθπ hη.le hbound⟩

end Erdos1151
