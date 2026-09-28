import Mathlib

noncomputable section
open scoped BigOperators

namespace Erdos1151

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι]

/-- A genuine finite weighted evaluation operator on continuous functions. -/
def finiteEvaluation (a : ι → X) (c : ι → ℝ) : C(X, ℝ) →L[ℝ] ℝ :=
  ∑ i, c i • ContinuousMap.evalCLM (R := ℝ) (a i)

@[simp] theorem finiteEvaluation_apply (a : ι → X) (c : ι → ℝ) (f : C(X, ℝ)) :
    finiteEvaluation a c f = ∑ i, c i * f (a i) := by
  simp [finiteEvaluation]

theorem finiteEvaluation_eq_zero (a : ι → X) (c : ι → ℝ) (f : C(X, ℝ))
    (hf : ∀ i, f (a i) = 0) : finiteEvaluation a c f = 0 := by
  simp [hf]

end Erdos1151
