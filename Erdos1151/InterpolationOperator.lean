import Erdos1151.ChebyshevWeights
import Erdos1151.TentChebyshev

noncomputable section
open Polynomial Filter Topology

namespace Erdos1151

abbrev Interval := Set.Icc (-1 : ℝ) 1

/-- The actual continuous linear interpolation functional at a fixed point. -/
def chebyshevOperator (x : ℝ) (n : ℕ) : C(Interval, ℝ) →L[ℝ] ℝ :=
  finiteEvaluation (nodePoint n) (fun k => coefficient n k x)

@[simp] theorem chebyshevOperator_apply (x : ℝ) (n : ℕ) (f : C(Interval, ℝ)) :
    chebyshevOperator x n f = ∑ k : Fin n, coefficient n k x * f (nodePoint n k) :=
  finiteEvaluation_apply _ _ _

/-- The unique polynomial with degree below the number of Chebyshev nodes. -/
def interpolationPolynomial (n : ℕ) (f : C(Interval, ℝ)) : ℝ[X] :=
  Lagrange.interpolate Finset.univ (node n) (fun k => f (nodePoint n k))

theorem interpolationPolynomial_degree (n : ℕ) (f : C(Interval, ℝ)) :
    (interpolationPolynomial n f).degree < n := by
  simpa only [interpolationPolynomial, Finset.card_univ, Fintype.card_fin] using
    Lagrange.degree_interpolate_lt (s := Finset.univ)
    (fun k => f (nodePoint n k)) (node_injective n).injOn

theorem interpolationPolynomial_node (n : ℕ) (f : C(Interval, ℝ)) (k : Fin n) :
    (interpolationPolynomial n f).eval (node n k) = f (nodePoint n k) :=
  Lagrange.eval_interpolate_at_node _ (node_injective n).injOn (Finset.mem_univ k)

theorem interpolationPolynomial_eval (n : ℕ) (f : C(Interval, ℝ)) (x : ℝ) :
    (interpolationPolynomial n f).eval x = chebyshevOperator x n f := by
  simp only [interpolationPolynomial, Lagrange.interpolate_apply,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    chebyshevOperator_apply, coefficient, mul_comm]

theorem chebyshevOperator_one (x : ℝ) (n : ℕ) (hn : 0 < n) :
    chebyshevOperator x n (1 : C(Interval, ℝ)) = 1 := by
  rw [← interpolationPolynomial_eval]
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  change (Lagrange.interpolate Finset.univ (node n) (1 : Fin n → ℝ)).eval x = 1
  rw [Lagrange.interpolate_one (node_injective n).injOn hne, Polynomial.eval_one]

/-- Folding an angle into `[0, pi]` preserves every integer cosine multiplier. -/
theorem cos_nat_arccos_cos (θ : ℝ) (n : ℕ) :
    Real.cos ((n : ℝ) * Real.arccos (Real.cos θ)) = Real.cos ((n : ℝ) * θ) := by
  have h := congrArg (fun x => (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x)
    (Real.cos_arccos (Real.neg_one_le_cos θ) (Real.cos_le_one θ))
  simpa only [Polynomial.Chebyshev.T_real_cos, Int.cast_natCast] using h

theorem rational_cos_normalized (p q : ℕ) (hq : Odd q) :
    ∃ θ : ℝ, θ ∈ Set.Icc 0 Real.pi ∧ Real.cos θ = Real.cos (p * Real.pi / q) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, δ ≤ |Real.cos ((n : ℝ) * θ)| := by
  obtain ⟨δ, hδ, hb⟩ := rational_cos_uniform_lower p q hq
  refine ⟨Real.arccos (Real.cos (p * Real.pi / q)),
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩,
    Real.cos_arccos (Real.neg_one_le_cos _) (Real.cos_le_one _), δ, hδ, ?_⟩
  intro n
  simpa only [cos_nat_arccos_cos] using hb n

end Erdos1151
