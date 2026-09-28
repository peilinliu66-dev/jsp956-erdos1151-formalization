import Mathlib

noncomputable section

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1151

/-- Reciprocal mass restricted to a predicate on a natural-number interval. -/
def goodReciprocalSum (P : ℕ → Prop) [DecidablePred P] (a b : ℕ) : ℝ :=
  ∑ m ∈ (Ico a b).filter P, 1 / (m : ℝ)

theorem goodReciprocalSum_nonneg (P : ℕ → Prop) [DecidablePred P] (a b : ℕ) :
    0 ≤ goodReciprocalSum P a b := by
  apply sum_nonneg
  intro m _
  positivity

theorem goodReciprocalSum_mono (P : ℕ → Prop) [DecidablePred P]
    {a b c d : ℕ} (hca : c ≤ a) (hbd : b ≤ d) :
    goodReciprocalSum P a b ≤ goodReciprocalSum P c d := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro m hm
    obtain ⟨hm, hp⟩ := mem_filter.mp hm
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hca.trans (mem_Ico.mp hm).1,
      (mem_Ico.mp hm).2.trans_le hbd⟩, hp⟩
  · intro m _ _
    positivity

theorem goodReciprocalSum_add (P : ℕ → Prop) [DecidablePred P]
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    goodReciprocalSum P a b + goodReciprocalSum P b c =
      goodReciprocalSum P a c := by
  simp only [goodReciprocalSum, sum_filter]
  exact sum_Ico_consecutive _ hab hbc

/-- Counting alone controls reciprocal mass in a shell. -/
theorem reciprocal_shell_card_bound (P : ℕ → Prop) [DecidablePred P]
    (M : ℕ) (hM : 0 < M) :
    (((Ico M (2 * M)).filter P).card : ℝ) / (2 * (M : ℝ)) ≤
      goodReciprocalSum P M (2 * M) := by
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  calc
    (((Ico M (2 * M)).filter P).card : ℝ) / (2 * (M : ℝ)) =
        ∑ m ∈ (Ico M (2 * M)).filter P, 1 / (2 * (M : ℝ)) := by
      simp [div_eq_mul_inv]
    _ ≤ goodReciprocalSum P M (2 * M) := by
      apply sum_le_sum
      intro m hm
      have hmI := mem_Ico.mp (mem_filter.mp hm).1
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hM.trans_le hmI.1
      have hmle : (m : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hmI.2.le
      exact one_div_le_one_div_of_le hmpos hmle

theorem reciprocal_shell_lower (P : ℕ → Prop) [DecidablePred P]
    (M : ℕ) (hM : 0 < M) (ρ : ℝ)
    (hcount : ρ * (M : ℝ) / 2 ≤ (((Ico M (2 * M)).filter P).card : ℝ)) :
    ρ / 4 ≤ goodReciprocalSum P M (2 * M) := by
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  calc
    ρ / 4 = (ρ * (M : ℝ) / 2) / (2 * (M : ℝ)) := by field_simp; ring
    _ ≤ (((Ico M (2 * M)).filter P).card : ℝ) / (2 * (M : ℝ)) :=
      div_le_div_of_nonneg_right hcount (by positivity)
    _ ≤ goodReciprocalSum P M (2 * M) := reciprocal_shell_card_bound P M hM

/-- The inclusion-exclusion error can be absorbed as soon as the shell starts
beyond `2 E / ρ`. No number-theoretic assumptions enter this reduction. -/
theorem reciprocal_shell_lower_of_error (P : ℕ → Prop) [DecidablePred P]
    (M : ℕ) (hM : 0 < M) (ρ E : ℝ)
    (hcount : ρ * (M : ℝ) - E ≤ (((Ico M (2 * M)).filter P).card : ℝ))
    (herr : 2 * E ≤ ρ * (M : ℝ)) :
    ρ / 4 ≤ goodReciprocalSum P M (2 * M) := by
  apply reciprocal_shell_lower P M hM ρ
  linarith

/-- Every dyadic shell contributes a fixed positive amount. -/
theorem reciprocal_dyadic_shells_lower (P : ℕ → Prop) [DecidablePred P]
    (M K : ℕ) (hM : 0 < M) (ρ : ℝ)
    (hcount : ∀ j < K, ρ * ((M * 2 ^ j : ℕ) : ℝ) / 2 ≤
      (((Ico (M * 2 ^ j) (2 * (M * 2 ^ j))).filter P).card : ℝ)) :
    (K : ℝ) * ρ / 4 ≤ goodReciprocalSum P M (M * 2 ^ K) := by
  induction K with
  | zero => simp [goodReciprocalSum]
  | succ K ih =>
    have hprev := ih (fun j hj => hcount j (Nat.lt_succ_of_lt hj))
    have hcur := reciprocal_shell_lower P (M * 2 ^ K) (by positivity) ρ
      (hcount K (Nat.lt_succ_self K))
    have hstart : M ≤ M * 2 ^ K := by
      exact Nat.le_mul_of_pos_right M (by positivity)
    have hend : M * 2 ^ K ≤ 2 * (M * 2 ^ K) := by omega
    have hadd := goodReciprocalSum_add P hstart hend
    have heq : M * 2 ^ (K + 1) = 2 * (M * 2 ^ K) := by rw [pow_succ]; ring
    rw [heq]
    push_cast
    linarith

/-- The natural dyadic logarithm captures all but one shell of a real logarithmic
interval. This avoids rounding real logarithms in the main application. -/
theorem dyadic_shell_count_log_lower (M N : ℕ) (hM : 0 < M) (hMN : M ≤ N) :
    (Real.log (N : ℝ) - Real.log (M : ℝ)) / Real.log 2 - 1 ≤
      (Nat.log 2 (N / M) : ℝ) := by
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hM.trans_le hMN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquot : N / M < 2 ^ (Nat.log 2 (N / M) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hupper : N < 2 ^ (Nat.log 2 (N / M) + 1) * M :=
    (Nat.div_lt_iff_lt_mul hM).mp hquot
  have hupperR : (N : ℝ) < (2 : ℝ) ^ (Nat.log 2 (N / M) + 1) * (M : ℝ) := by
    exact_mod_cast hupper
  have hl := Real.log_lt_log hNr hupperR
  rw [Real.log_mul (by positivity) hMr.ne', Real.log_pow] at hl
  push_cast at hl
  apply (sub_le_iff_le_add).2
  apply (div_le_iff₀ hlog2).2
  linarith

/-- A uniform positive-density estimate on long intervals forces logarithmic
reciprocal mass. The predicate may depend on an arbitrary fixed translation. -/
theorem reciprocal_log_lower (P : ℕ → Prop) [DecidablePred P]
    (M N : ℕ) (hM : 0 < M) (hMN : M ≤ N) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hcount : ∀ L : ℕ, M ≤ L → ρ * (L : ℝ) / 2 ≤
      (((Ico L (2 * L)).filter P).card : ℝ)) :
    (ρ / 4) * ((Real.log (N : ℝ) - Real.log (M : ℝ)) / Real.log 2 - 1) ≤
      goodReciprocalSum P M N := by
  let K := Nat.log 2 (N / M)
  have hquot : N / M ≠ 0 := by
    have : 1 ≤ N / M := (Nat.le_div_iff_mul_le hM).2 (by simpa using hMN)
    omega
  have hend : M * 2 ^ K ≤ N := by
    have hp := Nat.pow_log_le_self 2 hquot
    simpa [K, Nat.mul_comm] using (Nat.le_div_iff_mul_le hM).mp hp
  have hmass := reciprocal_dyadic_shells_lower P M K hM ρ (by
    intro j hj
    exact hcount (M * 2 ^ j) (Nat.le_mul_of_pos_right M (by positivity)))
  have hK := dyadic_shell_count_log_lower M N hM hMN
  have hmul := mul_le_mul_of_nonneg_left hK (div_nonneg hρ (by norm_num : (0:ℝ) ≤ 4))
  calc
    (ρ / 4) * ((Real.log (N : ℝ) - Real.log (M : ℝ)) / Real.log 2 - 1) ≤
        (K : ℝ) * ρ / 4 := by dsimp [K]; nlinarith
    _ ≤ goodReciprocalSum P M (M * 2 ^ K) := hmass
    _ ≤ goodReciprocalSum P M N := goodReciprocalSum_mono P le_rfl hend

theorem log_three_quarter_cutoff_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (Nat.ceil ((n : ℝ) ^ (3 / 4 : ℝ)) : ℝ) ≤
      Real.log 2 + (3 / 4 : ℝ) * Real.log (n : ℝ) := by
  have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hp1 : 1 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hnr (by norm_num)
  have hp0 : 0 < (n : ℝ) ^ (3 / 4 : ℝ) := by linarith
  have hceil := Nat.ceil_lt_add_one hp0.le
  have hceilpos : (0 : ℝ) < (Nat.ceil ((n : ℝ) ^ (3 / 4 : ℝ)) : ℝ) :=
    hp0.trans_le (Nat.le_ceil _)
  have hupper : (Nat.ceil ((n : ℝ) ^ (3 / 4 : ℝ)) : ℝ) ≤
      2 * (n : ℝ) ^ (3 / 4 : ℝ) := by linarith
  have hl := Real.log_le_log hceilpos hupper
  rwa [Real.log_mul (by norm_num) hp0.ne', Real.log_rpow hnpos] at hl

theorem log_linear_endpoint_ge (n : ℕ) {c : ℝ} (hc : 0 < c)
    (hcn : 2 ≤ c * (n : ℝ)) :
    Real.log c + Real.log (n : ℝ) - Real.log 2 ≤
      Real.log (Nat.floor (c * (n : ℝ)) : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos hc.le (le_of_not_gt h)
    linarith
  have hfloor := Nat.lt_floor_add_one (c * (n : ℝ))
  have hlow : c * (n : ℝ) / 2 ≤ (Nat.floor (c * (n : ℝ)) : ℝ) := by linarith
  have hl := Real.log_le_log (by positivity : 0 < c * (n : ℝ) / 2) hlow
  rwa [Real.log_div (mul_pos hc hnpos).ne' (by norm_num),
    Real.log_mul hc.ne' hnpos.ne'] at hl

/-- The explicit cutoff used in the primitive-node argument leaves a logarithmic
number of dyadic shells: from `ceil(n^(3/4))` to `floor(c n)`. -/
theorem reciprocal_three_quarter_lower (P : ℕ → Prop) [DecidablePred P]
    (n : ℕ) (hn : 1 ≤ n) {c ρ : ℝ} (hc : 0 < c) (hρ : 0 ≤ ρ)
    (hcn : 2 ≤ c * (n : ℝ))
    (hlarge : 8 * (3 * Real.log 2 - Real.log c) ≤ Real.log (n : ℝ))
    (hcount : ∀ L : ℕ, Nat.ceil ((n : ℝ) ^ (3 / 4 : ℝ)) ≤ L →
      ρ * (L : ℝ) / 2 ≤ (((Ico L (2 * L)).filter P).card : ℝ)) :
    ρ * Real.log (n : ℝ) / (32 * Real.log 2) ≤
      goodReciprocalSum P (Nat.ceil ((n : ℝ) ^ (3 / 4 : ℝ)))
        (Nat.floor (c * (n : ℝ))) := by
  let M := Nat.ceil ((n : ℝ) ^ (3 / 4 : ℝ))
  let N := Nat.floor (c * (n : ℝ))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hM : 0 < M := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnpos _)
  have hN : 0 < N := Nat.floor_pos.mpr (by linarith)
  have hlM := log_three_quarter_cutoff_le n hn
  have hlN := log_linear_endpoint_ge n hc hcn
  have hgap : Real.log (n : ℝ) / 8 + Real.log 2 ≤
      Real.log (N : ℝ) - Real.log (M : ℝ) := by
    dsimp [N, M]
    linarith
  have hMN : M ≤ N := by
    have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hlogMN : Real.log (M : ℝ) ≤ Real.log (N : ℝ) := by linarith
    exact_mod_cast (Real.log_le_log_iff hMr hNr).mp hlogMN
  have hbase := reciprocal_log_lower P M N hM hMN ρ hρ hcount
  have hratio : Real.log (n : ℝ) / (8 * Real.log 2) ≤
      (Real.log (N : ℝ) - Real.log (M : ℝ)) / Real.log 2 - 1 := by
    apply (le_sub_iff_add_le).2
    apply (le_div_iff₀ hlog2).2
    have heq : (Real.log (n : ℝ) / (8 * Real.log 2) + 1) * Real.log 2 =
        Real.log (n : ℝ) / 8 + Real.log 2 := by field_simp
    rwa [heq]
  have hmul := mul_le_mul_of_nonneg_left hratio (div_nonneg hρ (by norm_num : (0:ℝ) ≤ 4))
  have heq : ρ * Real.log (n : ℝ) / (32 * Real.log 2) =
      (ρ / 4) * (Real.log (n : ℝ) / (8 * Real.log 2)) := by ring
  rw [heq]
  exact hmul.trans hbase

/-- Version matching the output of inclusion-exclusion: the same absolute error
`E` applies to every translated shell, and it is absorbed at the real cutoff. -/
theorem reciprocal_three_quarter_lower_of_error (P : ℕ → Prop) [DecidablePred P]
    (n : ℕ) (hn : 1 ≤ n) {c ρ E : ℝ} (hc : 0 < c) (hρ : 0 ≤ ρ)
    (hcn : 2 ≤ c * (n : ℝ))
    (hlarge : 8 * (3 * Real.log 2 - Real.log c) ≤ Real.log (n : ℝ))
    (hcount : ∀ L : ℕ, Nat.ceil ((n : ℝ) ^ (3 / 4 : ℝ)) ≤ L →
      ρ * (L : ℝ) - E ≤ (((Ico L (2 * L)).filter P).card : ℝ))
    (herr : 2 * E ≤ ρ * (n : ℝ) ^ (3 / 4 : ℝ)) :
    ρ * Real.log (n : ℝ) / (32 * Real.log 2) ≤
      goodReciprocalSum P (Nat.ceil ((n : ℝ) ^ (3 / 4 : ℝ)))
        (Nat.floor (c * (n : ℝ))) := by
  apply reciprocal_three_quarter_lower P n hn hc hρ hcn hlarge
  intro L hL
  have hLreal : (n : ℝ) ^ (3 / 4 : ℝ) ≤ (L : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hL)
  have hmul := mul_le_mul_of_nonneg_left hLreal hρ
  have hcnt := hcount L hL
  linarith

end Erdos1151
