import Mathlib

/-!
The recursive sign argument in Erdős's 1943 correction.

This module proves an abstract, genuinely conditional construction lemma.
It is not an unconditional proof of Erdős problem 1151. The analytic
Chebyshev bump family and convergence hypotheses remain to be supplied.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace Erdos1151

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Partial sums whose next summand reinforces the current row's sign. -/
def signedPartial (L : ℕ → E →L[ℝ] ℝ) (v : ℕ → E) : ℕ → E
  | 0 => 0
  | n + 1 => signedPartial L v n +
      if 0 ≤ L n (signedPartial L v n) then v n else -v n

/-- The zero-prefix case deliberately uses +1, never signum(0). -/
def recursiveSign (L : ℕ → E →L[ℝ] ℝ) (v : ℕ → E) (n : ℕ) : ℝ :=
  if 0 ≤ L n (signedPartial L v n) then 1 else -1

theorem recursiveSign_cases (L : ℕ → E →L[ℝ] ℝ) (v : ℕ → E) (n : ℕ) :
    recursiveSign L v n = 1 ∨ recursiveSign L v n = -1 := by
  unfold recursiveSign
  split <;> simp

theorem signedPartial_eq_sum (L : ℕ → E →L[ℝ] ℝ) (v : ℕ → E) (n : ℕ) :
    signedPartial L v n = ∑ i ∈ Finset.range n, recursiveSign L v i • v i := by
  induction n with
  | zero => simp [signedPartial]
  | succ n ih =>
    rw [Finset.sum_range_succ, signedPartial, ← ih]
    by_cases h : 0 ≤ L n (signedPartial L v n)
    · simp [recursiveSign, h]
    · simp [recursiveSign, h]

theorem diagonal_lower_bound (L : ℕ → E →L[ℝ] ℝ) (v : ℕ → E) (n : ℕ)
    (hv : 0 ≤ L n (v n)) :
    L n (v n) ≤ |L n (signedPartial L v (n + 1))| := by
  rw [signedPartial]
  split_ifs with h
  · rw [map_add, abs_of_nonneg (add_nonneg h hv)]
    linarith
  · rw [map_add, map_neg, abs_of_nonpos (by linarith :
        L n (signedPartial L v n) + -L n (v n) ≤ 0)]
    linarith

theorem row_stabilizes (L : ℕ → E →L[ℝ] ℝ) (v : ℕ → E)
    (htri : ∀ n m, n < m → L n (v m) = 0) (n m : ℕ) (hnm : n + 1 ≤ m) :
    L n (signedPartial L v m) = L n (signedPartial L v (n + 1)) := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [signedPartial]
    split_ifs <;> simp [map_add, map_neg, htri n m (by omega), ih]

/-- A limit of the recursive partial sums inherits every diagonal lower bound. -/
theorem limit_diagonal_lower_bound (L : ℕ → E →L[ℝ] ℝ) (v : ℕ → E)
    (htri : ∀ n m, n < m → L n (v m) = 0)
    (hdiag : ∀ n, 0 ≤ L n (v n)) (f : E)
    (hf : Tendsto (signedPartial L v) atTop (𝓝 f)) (n : ℕ) :
    L n (v n) ≤ |L n f| := by
  have hevent : ∀ᶠ m in atTop,
      L n (signedPartial L v m) = L n (signedPartial L v (n + 1)) := by
    filter_upwards [eventually_ge_atTop (n + 1)] with m hm
    exact row_stabilizes L v htri n m hm
  have hlim : Tendsto (fun m => L n (signedPartial L v m)) atTop (𝓝 (L n f)) :=
    (L n).continuous.tendsto f |>.comp hf
  have hconst : Tendsto (fun m => L n (signedPartial L v m)) atTop
      (𝓝 (L n (signedPartial L v (n + 1)))) :=
    tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hevent)
  have heq := tendsto_nhds_unique hlim hconst
  rw [heq]
  exact diagonal_lower_bound L v n (hdiag n)

theorem strong_divergence_of_triangular_limit (L : ℕ → E →L[ℝ] ℝ) (v : ℕ → E)
    (htri : ∀ n m, n < m → L n (v m) = 0)
    (hdiag : ∀ n, 0 ≤ L n (v n)) (f : E)
    (hf : Tendsto (signedPartial L v) atTop (𝓝 f))
    (hgrowth : Tendsto (fun n => L n (v n)) atTop atTop) :
    Tendsto (fun n => |L n f|) atTop atTop := by
  apply tendsto_atTop_mono (fun n => limit_diagonal_lower_bound L v htri hdiag f hf n)
  exact hgrowth

end Erdos1151
