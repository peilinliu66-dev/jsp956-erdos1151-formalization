import Erdos1151.StrongDivergence
import Erdos1151.TentChebyshev
import Erdos1151.Weights

/-!
All geometric and convergence conditions of the triangular construction
are discharged here for actual Chebyshev nodes. The sole remaining premise
is the quantitative primitive coefficient mass growth; it is not an axiom.
-/

noncomputable section
open Filter Topology

namespace Erdos1151

theorem exists_divergence_of_primitive_mass_growth
    (w : (n : ℕ) → Fin n → ℝ)
    (hgrowth : Tendsto (fun n => amplitude n * primitiveMass n (w n)) atTop atTop) :
    ∃ f : C(Set.Icc (-1 : ℝ) 1, ℝ),
      Tendsto (fun n => |finiteEvaluation (nodePoint n) (w n) f|) atTop atTop := by
  let L := fun n => finiteEvaluation (nodePoint (n + 2)) (w (n + 2))
  let b := fun n => primitiveBump (n + 2) (w (n + 2))
  have hdec : ∀ n m, n < m → ∀ x, b n x ≠ 0 → b m x ≠ 0 →
      amplitude (m + 2) ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) * amplitude (n + 2) := by
    intro n m hnm x hn hm
    have hsp := primitiveBump_square_sparse (by omega : 0 < n + 2)
      (by omega : n + 2 < m + 2) (w (n + 2)) (w (m + 2)) x hn hm
    exact amplitude_square_contraction (n + 2) (m + 2) (by omega) hsp.le
  have htri : ∀ n m, n < m → L n (b m) = 0 := by
    intro n m hnm
    exact primitiveBump_triangular (by omega : n + 2 < m + 2) _ _
  have hdiag : ∀ n, 0 ≤ L n (b n) := by
    intro n
    dsimp [L, b]
    rw [primitiveBump_diagonal]
    exact primitiveMass_nonneg _ _
  have hgr : Tendsto (fun n => amplitude (n + 2) * L n (b n)) atTop atTop := by
    have h := hgrowth.comp (tendsto_add_atTop_nat 2)
    change Tendsto (fun n => amplitude (n + 2) * primitiveMass (n + 2) (w (n + 2)))
      atTop atTop at h
    simpa only [L, b, primitiveBump_diagonal] using h
  obtain ⟨f, hf⟩ := exists_strong_divergence_of_sparse_bumps
    L b (fun n => amplitude (n + 2)) contraction_factor_bounds.1.le
    contraction_factor_bounds.2 (fun n => amplitude_nonneg (n + 2))
    shifted_amplitude_antitone shifted_amplitude_tendsto_zero
    (fun n x => primitiveBump_abs_le_one (n + 2) (w (n + 2)) x) hdec htri hdiag hgr
  exact ⟨f, (tendsto_add_atTop_iff_nat 2).1 hf⟩

theorem exists_divergence_of_primitive_mass_lower
    (w : (n : ℕ) → Fin n → ℝ) {c : ℝ} (hc : 0 < c)
    (hmass : ∀ᶠ (n : ℕ) in atTop,
      c * (Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤ primitiveMass n (w n)) :
    ∃ f : C(Set.Icc (-1 : ℝ) 1, ℝ),
      Tendsto (fun n => |finiteEvaluation (nodePoint n) (w n) f|) atTop atTop :=
  exists_divergence_of_primitive_mass_growth w (weighted_mass_tendsto hc hmass)

end Erdos1151
