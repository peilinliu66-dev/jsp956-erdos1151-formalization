import Erdos1151.Tent
import Erdos1151.ChebyshevNodes
import Erdos1151.FiniteEvaluation

/-!
Actual primitive-node tent families. All geometric hypotheses of the generic
tent construction are discharged from Chebyshev-node separation.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1151

def primitiveNodes (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun k => Nat.Coprime (2 * k.val + 1) n

@[simp] theorem mem_primitiveNodes {n : ℕ} (k : Fin n) :
    k ∈ primitiveNodes n ↔ Primitive n k := by simp [primitiveNodes, Primitive]

def nodePoint (n : ℕ) (k : Fin n) : Set.Icc (-1 : ℝ) 1 :=
  ⟨node n k, (node_mem_Ioo n k).1.le, (node_mem_Ioo n k).2.le⟩

@[simp] theorem nodePoint_val (n : ℕ) (k : Fin n) : (nodePoint n k).val = node n k := rfl

/-- A real continuous function with signed tents at all primitive nodes of row `n`. -/
def primitiveBump (n : ℕ) (w : Fin n → ℝ) : C(Set.Icc (-1 : ℝ) 1, ℝ) :=
  tentRowMap (primitiveNodes n) (tentRadius n) (node n) w

/-- No regularity or sign condition on the row weights is assumed. -/
def primitiveMass (n : ℕ) (w : Fin n → ℝ) : ℝ := ∑ k ∈ primitiveNodes n, |w k|

theorem primitiveMass_nonneg (n : ℕ) (w : Fin n → ℝ) : 0 ≤ primitiveMass n w :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem primitiveBump_abs_le_one (n : ℕ) (w : Fin n → ℝ) (x : Set.Icc (-1 : ℝ) 1) :
    |primitiveBump n w x| ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [primitiveBump, tentRowMap, tentRow, primitiveNodes]
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  change |tentRow (primitiveNodes n) (tentRadius n) (node n) w x.val| ≤ 1
  apply tentRow_abs_le_one _ (tentRadius_pos hn0) (node n) w _ x.val
  intro i hi j hj hij
  exact (two_tentRadius_le_inverse_cube hn0).trans
    (node_separation i j le_rfl le_rfl (fun h => hij (node_injective n h)))

theorem primitiveBump_norm_le_one (n : ℕ) (w : Fin n → ℝ) :
    ‖primitiveBump n w‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1)).2
  exact primitiveBump_abs_le_one n w

theorem primitiveBump_at_node (n : ℕ) (w : Fin n → ℝ) (k : Fin n) :
    primitiveBump n w (nodePoint n k) =
      if k ∈ primitiveNodes n then tentSign (w k) else 0 := by
  classical
  have hn : 0 < n := Nat.zero_lt_of_lt k.isLt
  change tentRow (primitiveNodes n) (tentRadius n) (node n) w (node n k) = _
  apply tentRow_at_node _ (tentRadius_pos hn) (node n) w k
  intro i hi hik
  have hrad : tentRadius n ≤ 2 * tentRadius n := by linarith [tentRadius_pos hn]
  exact (hrad.trans (two_tentRadius_le_inverse_cube hn)).trans
    (node_separation k i le_rfl le_rfl (fun h => hik (node_injective n h).symm))

/-- Every strictly future row vanishes exactly at every present node. -/
theorem primitiveBump_at_earlier_node {n m : ℕ} (hnm : n < m)
    (w : Fin m → ℝ) (k : Fin n) : primitiveBump m w (nodePoint n k) = 0 := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hnm
  change tentRow (primitiveNodes m) (tentRadius m) (node m) w (node n k) = 0
  apply tentRow_zero_of_far _ (tentRadius_pos hm) (node m) w
  intro j hj
  have hrad : tentRadius m ≤ 2 * tentRadius m := by linarith [tentRadius_pos hm]
  exact (hrad.trans (two_tentRadius_le_inverse_cube hm)).trans
    (node_separation k j hnm.le le_rfl
      (Ne.symm (primitive_ne_earlier j k ((mem_primitiveNodes j).1 hj) hnm)))

/-- The actual finite evaluation operator has precisely the selected absolute mass. -/
theorem primitiveBump_diagonal (n : ℕ) (w : Fin n → ℝ) :
    finiteEvaluation (nodePoint n) w (primitiveBump n w) = primitiveMass n w := by
  by_cases hn : n = 0
  · subst n
    simp [primitiveMass, primitiveNodes]
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  rw [finiteEvaluation_apply]
  change (∑ j, w j * tentRow (primitiveNodes n) (tentRadius n) (node n) w (node n j)) =
    ∑ j ∈ primitiveNodes n, |w j|
  apply tentRow_diagonal _ (tentRadius_pos hn0) (node n) w
  intro j i hi hij
  have hrad : tentRadius n ≤ 2 * tentRadius n := by linarith [tentRadius_pos hn0]
  exact (hrad.trans (two_tentRadius_le_inverse_cube hn0)).trans
    (node_separation j i le_rfl le_rfl (fun h => hij (node_injective n h).symm))

/-- The triangular cancellation is an exact equality of continuous linear evaluations. -/
theorem primitiveBump_triangular {n m : ℕ} (hnm : n < m)
    (v : Fin n → ℝ) (w : Fin m → ℝ) :
    finiteEvaluation (nodePoint n) v (primitiveBump m w) = 0 := by
  apply finiteEvaluation_eq_zero
  exact primitiveBump_at_earlier_node hnm w

/-- Two distinct active rows at one spatial point are separated by square growth. -/
theorem primitiveBump_square_sparse {n m : ℕ} (hn : 0 < n) (hnm : n < m)
    (v : Fin n → ℝ) (w : Fin m → ℝ) (x : Set.Icc (-1 : ℝ) 1)
    (hnx : primitiveBump n v x ≠ 0) (hmx : primitiveBump m w x ≠ 0) : n ^ 2 < m := by
  apply tentRows_square_sparse (primitiveNodes n) (primitiveNodes m) hn hnm
    (node n) v (node m) w x.val _ hnx hmx
  intro i hi j hj
  exact node_separation i j hnm.le le_rfl
    (Ne.symm (primitive_ne_earlier j i ((mem_primitiveNodes j).1 hj) hnm))

end Erdos1151
