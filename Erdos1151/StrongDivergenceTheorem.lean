import Erdos1151.ChebyshevMass
import Erdos1151.ChebyshevDivergence
import Erdos1151.InterpolationOperator
import Erdos1151.ChebyshevMassAll

/-!
Actual strong divergence for Chebyshev interpolation. All node geometry,
primitive counting, mass growth, convergence and recursive signs are proved
in the imported modules. The nonempty-cluster-set branch is separate.
-/

noncomputable section
open Filter Topology

namespace Erdos1151

theorem exists_chebyshev_strong_divergence (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi)
    (hcos : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, δ ≤ |Real.cos ((n : ℝ) * θ)|) :
    ∃ f : C(Interval, ℝ),
      Tendsto (fun n => |chebyshevOperator (Real.cos θ) n f|) atTop atTop := by
  obtain ⟨c, hc, hmass⟩ := exists_primitiveMass_lower θ hθ hcos
  exact exists_divergence_of_primitive_mass_lower
    (fun n k => coefficient n k (Real.cos θ)) hc hmass

theorem rational_chebyshev_strong_divergence_all (p q : ℕ) (hq : Odd q) :
    ∃ f : C(Interval, ℝ),
      Tendsto (fun n => |chebyshevOperator (Real.cos (p * Real.pi / q)) n f|)
        atTop atTop := by
  obtain ⟨θ, hθ, hx, hcos⟩ := rational_cos_normalized p q hq
  simpa only [hx] using exists_chebyshev_strong_divergence θ hθ hcos

theorem exists_chebyshev_strong_divergence_interior (θ : ℝ)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hcos : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, δ ≤ |Real.cos ((n : ℝ) * θ)|) :
    ∃ f : C(Interval, ℝ),
      Tendsto (fun n => |chebyshevOperator (Real.cos θ) n f|) atTop atTop := by
  obtain ⟨c, hc, hmass⟩ := exists_interior_mass_lower θ hθ0 hθπ hcos
  exact exists_divergence_of_primitive_mass_lower
    (fun n k => coefficient n k (Real.cos θ)) hc hmass

/-- The corrected Erdős theorem at each interior rational-cosine point with
odd denominator. The numerator need not be odd or coprime to the denominator. -/
theorem rational_chebyshev_strong_divergence (p q : ℕ)
    (hp : 0 < p) (hpq : p < q) (hq : Odd q) :
    ∃ f : C(Interval, ℝ),
      Tendsto (fun n => |chebyshevOperator (Real.cos (p * Real.pi / q)) n f|)
        atTop atTop := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hpqr : (p : ℝ) < q := by exact_mod_cast hpq
  apply exists_chebyshev_strong_divergence_interior
    (p * Real.pi / q) (div_pos (mul_pos hpr Real.pi_pos) hqr)
  · apply (div_lt_iff₀ hqr).2
    nlinarith [Real.pi_pos]
  · exact rational_cos_uniform_lower p q hq

theorem rational_chebyshev_empty_cluster (p q : ℕ)
    (hp : 0 < p) (hpq : p < q) (hq : Odd q) :
    ∃ f : C(Interval, ℝ),
      finiteClusterSet (fun n => chebyshevOperator (Real.cos (p * Real.pi / q)) n f) = ∅ := by
  obtain ⟨f, hf⟩ := rational_chebyshev_strong_divergence p q hp hpq hq
  exact ⟨f, finiteClusterSet_eq_empty_of_abs_tendsto_atTop hf⟩

end Erdos1151
