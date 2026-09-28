import Erdos1151.ChebyshevEndpoints
import Erdos1151.ChebyshevAtomNormalization

noncomputable section
open Filter Topology

namespace Erdos1151

theorem exists_primitiveMass_lower (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi)
    (hcos : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, δ ≤ |Real.cos ((n : ℝ) * θ)|) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤
        primitiveMass n (fun k => coefficient n k (Real.cos θ)) := by
  by_cases h0 : θ = 0
  · subst θ
    simpa only [Real.cos_zero] using exists_endpoint_mass_lower 1 (Or.inr rfl)
  by_cases hπ : θ = Real.pi
  · subst θ
    simpa only [Real.cos_pi] using exists_endpoint_mass_lower (-1) (Or.inl rfl)
  exact exists_interior_mass_lower θ
    (lt_of_le_of_ne hθ.1 (Ne.symm h0)) (lt_of_le_of_ne hθ.2 hπ) hcos

theorem layerMass_tendsto (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi)
    (hcos : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, δ ≤ |Real.cos ((n : ℝ) * θ)|) :
    Tendsto (fun n => NonemptyAssembly.layerMass n θ) atTop atTop := by
  obtain ⟨c, hc, hmass⟩ := exists_primitiveMass_lower θ hθ hcos
  exact NonemptyAssembly.layerMass_tendsto_of_lower θ c hc hmass

end Erdos1151
