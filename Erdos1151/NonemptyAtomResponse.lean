import Erdos1151.ChebyshevAtomNormalization
import Erdos1151.NonemptyNodes

/-! Exact row responses of normalized primitive atoms and their finite Möbius sum. -/

noncomputable section
open scoped BigOperators

namespace Erdos1151.NonemptyAssembly

def atomResponse (m d : ℕ) (θ : ℝ) : ℝ :=
  ∑ j : Fin m, coefficient m j (Real.cos θ) * primitiveAtom d θ (angle m j)

theorem atomResponse_of_odd_quotient {d m : ℕ} (θ : ℝ)
    (hd : d ∣ m) (hodd : Odd (m / d))
    (hmass : layerMass d θ ≠ 0)
    (hcos : Real.cos ((d : ℝ) * θ) ≠ 0)
    (hpoint : ∀ k : Fin d, Real.cos θ ≠ node d k) :
    atomResponse m d θ =
      (d : ℝ) / m * oddCharacter (m / d) *
        Real.cos ((m : ℝ) * θ) / Real.cos ((d : ℝ) * θ) := by
  classical
  let γ : ℝ := (d : ℝ) / m * oddCharacter (m / d) *
    Real.cos ((m : ℝ) * θ) / Real.cos ((d : ℝ) * θ)
  unfold atomResponse primitiveAtom
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterms : ∀ k ∈ primitiveNodes d,
      (∑ j : Fin m, coefficient m j (Real.cos θ) *
        (if angle d k = angle m j then
          tentSign (coefficient d k (Real.cos θ)) / layerMass d θ else 0)) =
      γ * (|coefficient d k (Real.cos θ)| / layerMass d θ) := by
    intro k hk
    obtain ⟨j, hj⟩ := (primitive_occurs_iff k (mem_primitiveNodes k |>.mp hk)).mpr
      ⟨m / d, hodd, (Nat.mul_div_cancel' hd).symm⟩
    have hang : angle d k = angle m j :=
      Real.strictAntiOn_cos.injOn (angle_mem_Icc d k) (angle_mem_Icc m j) hj
    rw [Finset.sum_eq_single j]
    · rw [if_pos hang, primitive_coefficient_transfer k j θ
        (mem_primitiveNodes k |>.mp hk) hj (hpoint k) hcos]
      change γ * coefficient d k (Real.cos θ) *
        (tentSign (coefficient d k (Real.cos θ)) / layerMass d θ) = _
      rw [mul_assoc, ← mul_div_assoc, mul_tentSign]
    · intro l hl hlj
      have hne : angle d k ≠ angle m l := by
        intro h
        exact hlj (angle_injective m (h.symm.trans hang))
      rw [if_neg hne, mul_zero]
    · simp
  simp_rw [Finset.sum_congr rfl hterms]
  rw [← Finset.mul_sum, ← Finset.sum_div]
  change γ * (layerMass d θ / layerMass d θ) = γ
  rw [div_self hmass, mul_one]

theorem atomResponse_of_not_odd_multiple {d m : ℕ} (θ : ℝ)
    (hno : ¬∃ s, Odd s ∧ m = d * s) : atomResponse m d θ = 0 := by
  classical
  unfold atomResponse
  apply Finset.sum_eq_zero
  intro j hj
  have hz : primitiveAtom d θ (angle m j) = 0 := by
    apply primitiveAtom_zero_of_not_mem
    intro hmem
    obtain ⟨k, hk, hkα⟩ := Finset.mem_image.mp hmem
    apply hno
    apply (primitive_occurs_iff k (mem_primitiveNodes k |>.mp hk)).mp
    exact ⟨j, congrArg Real.cos hkα⟩
  rw [hz, mul_zero]

theorem atomResponse_layer {n u s : ℕ} (hn : 0 < n) (hu : Odd u) (hsu : s ∣ u)
    (θ : ℝ) (hmass : layerMass (n * s) θ ≠ 0)
    (hcos : Real.cos (((n * s : ℕ) : ℝ) * θ) ≠ 0)
    (hpoint : ∀ k : Fin (n * s), Real.cos θ ≠ node (n * s) k) :
    atomResponse (n * u) (n * s) θ = layerTransfer n u s θ := by
  have hdiv : n * s ∣ n * u := Nat.mul_dvd_mul_left n hsu
  have hodd : Odd ((n * u) / (n * s)) := by
    rw [Nat.mul_div_mul_left _ _ hn]
    exact hu.of_dvd_nat (Nat.div_dvd_of_dvd hsu)
  rw [atomResponse_of_odd_quotient θ hdiv hodd hmass hcos hpoint]
  unfold layerTransfer
  rw [Nat.mul_div_mul_left _ _ hn]
  push_cast
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [mul_div_mul_left _ _ hnR]

theorem atomResponse_layer_zero {n u s : ℕ} (hn : 0 < n) (hndvd : ¬s ∣ u) (θ : ℝ) :
    atomResponse (n * u) (n * s) θ = 0 := by
  apply atomResponse_of_not_odd_multiple
  rintro ⟨t, ht, h⟩
  apply hndvd
  refine ⟨t, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left hn
  simpa only [mul_assoc] using h

end Erdos1151.NonemptyAssembly
