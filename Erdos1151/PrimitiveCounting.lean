import Mathlib

/-!
Elementary finite counting and product estimates for the primitive
Chebyshev nodes in Erdős's strong-divergence construction.
-/

noncomputable section

open scoped BigOperators

namespace Erdos1151

/-- The loss from one odd denominator is bounded by a telescoping factor. -/
theorem odd_density_factor_sq (i : ℕ) (p : ℝ)
    (hp : 2 * (i : ℝ) + 3 ≤ p) :
    2 * (i : ℝ) + 1 ≤ (2 * (i : ℝ) + 3) * (1 - 1 / p) ^ 2 := by
  have hp0 : 0 < p := by have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i; linarith
  have heq : 1 - 1 / p = (p - 1) / p := by field_simp
  rw [heq, div_pow, ← mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hp0)).2
  have hmul : 0 ≤ p * (p - (2 * (i : ℝ) + 3)) :=
    mul_nonneg hp0.le (sub_nonneg.mpr hp)
  nlinarith

/-- A completely elementary lower bound for a product over increasing odd
denominators. Its hypothesis is supplied by sorting the distinct odd primes. -/
theorem odd_density_sq_lower (p : ℕ → ℝ) (k : ℕ)
    (hp : ∀ i < k, 2 * (i : ℝ) + 3 ≤ p i) :
    1 ≤ (2 * (k : ℝ) + 1) *
      (∏ i ∈ Finset.range k, (1 - 1 / p i)) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := ih (fun i hi => hp i (Nat.lt_succ_of_lt hi))
    have hf := odd_density_factor_sq k (p k) (hp k (Nat.lt_succ_self k))
    have hsq : 0 ≤ (∏ i ∈ Finset.range k, (1 - 1 / p i)) ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hf hsq
    rw [Finset.prod_range_succ]
    push_cast
    nlinarith

/-- A square-form lower bound avoids introducing square roots in the
finite-prime-product stage. -/
theorem odd_density_lower_recip_sq (p : ℕ → ℝ) (k : ℕ)
    (hp : ∀ i < k, 2 * (i : ℝ) + 3 ≤ p i) :
    1 / (2 * (k : ℝ) + 1) ≤
      (∏ i ∈ Finset.range k, (1 - 1 / p i)) ^ 2 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (k : ℝ) + 1)).2
  simpa [mul_comm] using odd_density_sq_lower p k hp

/-- Distinct odd integers at least three have the elementary ordered bound. -/
theorem ordered_odd_lower (P : Finset ℕ)
    (hP : ∀ p ∈ P, Odd p ∧ 3 ≤ p) (i : Fin P.card) :
    2 * i.val + 3 ≤ P.orderEmbOfFin rfl i := by
  have haux : ∀ j (hj : j < P.card),
      2 * j + 3 ≤ P.orderEmbOfFin rfl ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact (hP _ (P.orderEmbOfFin_mem rfl ⟨0, hj⟩)).2
    | succ j ih =>
      intro hj
      have hj' : j < P.card := Nat.lt_trans (Nat.lt_succ_self j) hj
      have hprev := ih hj'
      have hlt : P.orderEmbOfFin rfl ⟨j, hj'⟩ <
          P.orderEmbOfFin rfl ⟨j + 1, hj⟩ :=
        (P.orderEmbOfFin rfl).strictMono (by simp)
      obtain ⟨a, ha⟩ := (hP _ (P.orderEmbOfFin_mem rfl ⟨j, hj'⟩)).1
      obtain ⟨b, hb⟩ := (hP _ (P.orderEmbOfFin_mem rfl ⟨j + 1, hj⟩)).1
      omega
  exact haux i.val i.isLt

/-- The product bound in its actual finite-set form; primality is not needed,
only distinct odd denominators at least three. -/
theorem odd_finset_density_sq_lower (P : Finset ℕ)
    (hP : ∀ p ∈ P, Odd p ∧ 3 ≤ p) :
    1 ≤ (2 * (P.card : ℝ) + 1) *
      (∏ p ∈ P, (1 - 1 / (p : ℝ))) ^ 2 := by
  let seq : ℕ → ℝ := fun i =>
    if hi : i < P.card then (P.orderEmbOfFin rfl ⟨i, hi⟩ : ℝ) else 0
  have hseq : ∀ i < P.card, 2 * (i : ℝ) + 3 ≤ seq i := by
    intro i hi
    simp only [seq, dif_pos hi]
    exact_mod_cast ordered_odd_lower P hP ⟨i, hi⟩
  have hp := odd_density_sq_lower seq P.card hseq
  have hprod : (∏ i ∈ Finset.range P.card, (1 - 1 / seq i)) =
      ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
    rw [← Fin.prod_univ_eq_prod_range]
    simp only [seq, dif_pos (Fin.isLt _)]
    conv_rhs => rw [← P.map_orderEmbOfFin_univ rfl, Finset.prod_map]
    rfl
  rwa [hprod] at hp

/-- Only odd prime factors matter for a number of the form `2k+1`. -/
def oddPrimeFactors (n : ℕ) : Finset ℕ := n.primeFactors.filter (fun p => p ≠ 2)

theorem mem_oddPrimeFactors_spec {n p : ℕ} (hp : p ∈ oddPrimeFactors n) :
    p.Prime ∧ p ∣ n ∧ Odd p ∧ 3 ≤ p := by
  have hmem := Finset.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hmem.1
  refine ⟨hprime, Nat.dvd_of_mem_primeFactors hmem.1,
    hprime.odd_of_ne_two hmem.2, ?_⟩
  have := hprime.two_le
  omega

def primitiveDensity (n : ℕ) : ℝ :=
  ∏ p ∈ oddPrimeFactors n, (1 - 1 / (p : ℝ))

theorem primitiveDensity_sq_lower (n : ℕ) :
    1 ≤ (2 * ((oddPrimeFactors n).card : ℝ) + 1) * primitiveDensity n ^ 2 := by
  apply odd_finset_density_sq_lower
  intro p hp
  exact (mem_oddPrimeFactors_spec hp).2.2

theorem primitiveDensity_pos (n : ℕ) : 0 < primitiveDensity n := by
  apply Finset.prod_pos
  intro p hp
  have hthree : (3 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (mem_oddPrimeFactors_spec hp).2.2.2
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have : (1 : ℝ) / (p : ℝ) < 1 := by
    apply (div_lt_one hp0).2
    linarith
  linarith

theorem oddPrimeFactors_three_pow_le {n : ℕ} (hn : 0 < n) :
    3 ^ (oddPrimeFactors n).card ≤ n := by
  have hdvd : (∏ p ∈ oddPrimeFactors n, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd n)
  calc
    3 ^ (oddPrimeFactors n).card = ∏ _p ∈ oddPrimeFactors n, 3 := by simp
    _ ≤ ∏ p ∈ oddPrimeFactors n, p := by
      apply Finset.prod_le_prod (fun _ _ => by norm_num)
      intro p hp
      exact (mem_oddPrimeFactors_spec hp).2.2.2
    _ ≤ n := Nat.le_of_dvd hn hdvd

/-- Cubing the inclusion-exclusion error avoids an irrational exponent. -/
theorem oddPrimeFactors_error_cube_le {n : ℕ} (hn : 0 < n) :
    (2 ^ (oddPrimeFactors n).card) ^ 3 ≤ n ^ 2 := by
  have h3 := oddPrimeFactors_three_pow_le hn
  calc
    (2 ^ (oddPrimeFactors n).card) ^ 3 = 8 ^ (oddPrimeFactors n).card := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    _ ≤ 9 ^ (oddPrimeFactors n).card := Nat.pow_le_pow_left (by norm_num : 8 ≤ 9) _
    _ = (3 ^ (oddPrimeFactors n).card) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    _ ≤ n ^ 2 := Nat.pow_le_pow_left h3 _

/-- A residue class occupies an arbitrary interval with error at most one. -/
theorem residue_count_error (a M d r : ℕ) (hd : 0 < d) :
    |(((Finset.Ico a (a + M)).filter (fun k => Nat.ModEq d k r)).card : ℝ) -
      (M : ℝ) / (d : ℝ)| ≤ 1 := by
  let A : ℚ := ((a : ℚ) - (r : ℚ)) / (d : ℚ)
  let B : ℚ := (((a + M : ℕ) : ℚ) - (r : ℚ)) / (d : ℚ)
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hAB : A ≤ B := by dsimp [A, B]; gcongr; omega
  have hc : (((Finset.Ico a (a + M)).filter (fun k => Nat.ModEq d k r)).card : ℤ) =
      Int.ceil B - Int.ceil A := by
    rw [Nat.Ico_filter_modEq_card a (a + M) hd r]
    exact max_eq_left (sub_nonneg.mpr (Int.ceil_mono hAB))
  have hcq : (((Finset.Ico a (a + M)).filter (fun k => Nat.ModEq d k r)).card : ℚ) =
      (Int.ceil B : ℚ) - (Int.ceil A : ℚ) := by exact_mod_cast hc
  have hdiff : B - A = (M : ℚ) / (d : ℚ) := by dsimp [A, B]; push_cast; ring
  have hAlo := Int.le_ceil A
  have hAhi := Int.ceil_lt_add_one A
  have hBlo := Int.le_ceil B
  have hBhi := Int.ceil_lt_add_one B
  have hbound :
      |(((Finset.Ico a (a + M)).filter (fun k => Nat.ModEq d k r)).card : ℚ) -
        (M : ℚ) / (d : ℚ)| ≤ 1 := by
    rw [hcq, abs_le]
    constructor <;> linarith
  have hh := (Rat.cast_le (K := ℝ)).2 hbound
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_one] using hh

theorem odd_dvd_affine_iff (d k : ℕ) (hd : Odd d) :
    d ∣ 2 * k + 1 ↔ Nat.ModEq d k (d / 2) := by
  have heq : 2 * (d / 2) + 1 = d := by obtain ⟨t, ht⟩ := hd; omega
  have hbase : Nat.ModEq d (2 * (d / 2) + 1) 0 := by
    rw [heq]
    exact (dvd_refl d).modEq_zero_nat
  constructor
  · intro h
    have hfull := h.modEq_zero_nat.trans hbase.symm
    have hmul := Nat.ModEq.add_right_cancel' 1 hfull
    exact Nat.ModEq.cancel_left_of_coprime hd.coprime_two_right hmul
  · intro h
    exact Nat.modEq_zero_iff_dvd.mp ((h.mul_left 2).add_right 1 |>.trans hbase)

theorem affine_dvd_count_error (a M d : ℕ) (hd : Odd d) :
    |(((Finset.Ico a (a + M)).filter (fun k => d ∣ 2 * k + 1)).card : ℝ) -
      (M : ℝ) / (d : ℝ)| ≤ 1 := by
  have hd0 : 0 < d := by obtain ⟨t, ht⟩ := hd; omega
  simpa only [odd_dvd_affine_iff d _ hd] using residue_count_error a M d (d / 2) hd0

private theorem subtype_filter_card (I : Finset ℕ) (pred : ℕ → Prop)
    [DecidablePred pred] :
    (Finset.univ.filter (fun k : I => pred k.val)).card = (I.filter pred).card := by
  classical
  apply Finset.card_bij (fun k _ => k.val)
  · intro k hk
    exact Finset.mem_filter.mpr ⟨k.property, (Finset.mem_filter.mp hk).2⟩
  · intro k hk l hl heq
    exact Subtype.ext heq
  · intro k hk
    refine ⟨⟨k, (Finset.mem_filter.mp hk).1⟩, ?_, rfl⟩
    simpa using (Finset.mem_filter.mp hk).2

/-- Inclusion-exclusion for avoiding finitely many predicates on an interval.
This identity contains no analytic or distributional assumptions. -/
theorem avoid_count_inclusion_exclusion (I P : Finset ℕ) (bad : ℕ → ℕ → Prop)
    [DecidableRel bad] :
    ((I.filter (fun k => ∀ p ∈ P, ¬bad p k)).card : ℝ) =
      ∑ Q ∈ P.powerset, (-1 : ℝ) ^ Q.card *
        ((I.filter (fun k => ∀ p ∈ Q, bad p k)).card : ℝ) := by
  classical
  let S : ℕ → Finset I := fun p => Finset.univ.filter (fun k : I => bad p k.val)
  have hi : (P.inf (fun p => (S p)ᶜ)).card =
      (I.filter (fun k => ∀ p ∈ P, ¬bad p k)).card := by
    have heq : P.inf (fun p => (S p)ᶜ) =
        Finset.univ.filter (fun k : I => ∀ p ∈ P, ¬bad p k.val) := by
      ext k
      induction P using Finset.induction_on with
      | empty => simp
      | @insert p P hp ih => simp_all [Finset.inf_insert, S]
    rw [heq]
    exact subtype_filter_card I (fun k => ∀ p ∈ P, ¬bad p k)
  have hq (Q : Finset ℕ) : (Q.inf S).card =
      (I.filter (fun k => ∀ p ∈ Q, bad p k)).card := by
    have heq : Q.inf S = Finset.univ.filter (fun k : I => ∀ p ∈ Q, bad p k.val) := by
      ext k
      induction Q using Finset.induction_on with
      | empty => simp
      | @insert p Q hp ih => simp_all [Finset.inf_insert, S]
    rw [heq]
    exact subtype_filter_card I (fun k => ∀ p ∈ Q, bad p k)
  have h := Finset.inclusion_exclusion_sum_inf_compl (G := ℝ) P S (fun _ => 1)
  simpa [hi, hq, zsmul_eq_mul] using h

theorem coprime_affine_iff_avoid {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (2 * k + 1).Coprime n ↔ ∀ p ∈ oddPrimeFactors n, ¬p ∣ 2 * k + 1 := by
  constructor
  · intro h p hp hdiv
    have hspec := mem_oddPrimeFactors_spec hp
    exact hspec.1.ne_one (Nat.eq_one_of_dvd_coprimes h hdiv hspec.2.1)
  · intro h
    by_contra hc
    obtain ⟨p, hp, hpk, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hp2 : p ≠ 2 := by intro heq; subst p; omega
    have hpP : p ∈ oddPrimeFactors n :=
      Finset.mem_filter.mpr ⟨hp.mem_primeFactors hpn hn.ne', hp2⟩
    exact h p hpP hpk

theorem prime_product_dvd_iff (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) {b : ℕ} (hb : 0 < b) :
    (∀ p ∈ Q, p ∣ b) ↔ (∏ p ∈ Q, p) ∣ b := by
  constructor
  · intro h
    have hsub : Q ⊆ b.primeFactors := by
      intro p hp
      exact (hQ p hp).mem_primeFactors (h p hp) hb.ne'
    exact (Finset.prod_dvd_prod_of_subset _ _ _ hsub).trans (Nat.prod_primeFactors_dvd b)
  · intro h p hp
    exact (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp).trans h

theorem odd_finset_product (Q : Finset ℕ) (hQ : ∀ p ∈ Q, Odd p) :
    Odd (∏ p ∈ Q, p) := by
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert p Q hp ih =>
    rw [Finset.prod_insert hp]
    exact (hQ p (by simp)).mul (ih (fun q hq => hQ q (by simp [hq])))

theorem primitiveDensity_expansion (n : ℕ) :
    primitiveDensity n =
      ∑ Q ∈ (oddPrimeFactors n).powerset,
        (-1 : ℝ) ^ Q.card / ((∏ p ∈ Q, p : ℕ) : ℝ) := by
  unfold primitiveDensity
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro Q hQ
  simp [div_eq_mul_inv]

theorem primitive_count_inclusion_exclusion (a M n : ℕ) (hn : 0 < n) :
    (((Finset.Ico a (a + M)).filter (fun k => (2 * k + 1).Coprime n)).card : ℝ) =
      ∑ Q ∈ (oddPrimeFactors n).powerset, (-1 : ℝ) ^ Q.card *
        (((Finset.Ico a (a + M)).filter
          (fun k => (∏ p ∈ Q, p) ∣ 2 * k + 1)).card : ℝ) := by
  have hfilter : (Finset.Ico a (a + M)).filter (fun k => (2 * k + 1).Coprime n) =
      (Finset.Ico a (a + M)).filter (fun k => ∀ p ∈ oddPrimeFactors n, ¬p ∣ 2 * k + 1) := by
    ext k
    simp only [Finset.mem_filter, coprime_affine_iff_avoid hn k]
  rw [hfilter]
  rw [avoid_count_inclusion_exclusion]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hsub := Finset.mem_powerset.mp hQ
  have hprime : ∀ p ∈ Q, p.Prime := fun p hp => (mem_oddPrimeFactors_spec (hsub hp)).1
  have heq : (Finset.Ico a (a + M)).filter (fun k => ∀ p ∈ Q, p ∣ 2 * k + 1) =
      (Finset.Ico a (a + M)).filter (fun k => (∏ p ∈ Q, p) ∣ 2 * k + 1) := by
    ext k
    simp only [Finset.mem_filter, prime_product_dvd_iff Q hprime (by omega : 0 < 2 * k + 1)]
  rw [heq]

/-- The elementary sieve estimate for actual primitive Chebyshev indices,
uniform over every interval start and length. -/
theorem primitive_count_error (a M n : ℕ) (hn : 0 < n) :
    |(((Finset.Ico a (a + M)).filter (fun k => (2 * k + 1).Coprime n)).card : ℝ) -
      (M : ℝ) * primitiveDensity n| ≤ (2 : ℝ) ^ (oddPrimeFactors n).card := by
  let cnt : Finset ℕ → ℝ := fun Q =>
    (((Finset.Ico a (a + M)).filter
      (fun k => (∏ p ∈ Q, p) ∣ 2 * k + 1)).card : ℝ)
  have heq :
      (((Finset.Ico a (a + M)).filter (fun k => (2 * k + 1).Coprime n)).card : ℝ) -
        (M : ℝ) * primitiveDensity n =
      ∑ Q ∈ (oddPrimeFactors n).powerset, (-1 : ℝ) ^ Q.card *
        (cnt Q - (M : ℝ) / ((∏ p ∈ Q, p : ℕ) : ℝ)) := by
    rw [primitive_count_inclusion_exclusion a M n hn, primitiveDensity_expansion,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro Q hQ
    dsimp [cnt]
    ring
  rw [heq]
  calc
    |∑ Q ∈ (oddPrimeFactors n).powerset, (-1 : ℝ) ^ Q.card *
        (cnt Q - (M : ℝ) / ((∏ p ∈ Q, p : ℕ) : ℝ))| ≤
      ∑ Q ∈ (oddPrimeFactors n).powerset,
        |(-1 : ℝ) ^ Q.card * (cnt Q - (M : ℝ) / ((∏ p ∈ Q, p : ℕ) : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _Q ∈ (oddPrimeFactors n).powerset, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro Q hQ
      have hsub := Finset.mem_powerset.mp hQ
      have hodd : Odd (∏ p ∈ Q, p) := odd_finset_product Q
        (fun p hp => (mem_oddPrimeFactors_spec (hsub hp)).2.2.1)
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, cnt]
        using affine_dvd_count_error a M (∏ p ∈ Q, p) hodd
    _ = (2 : ℝ) ^ (oddPrimeFactors n).card := by simp

theorem primitive_count_lower (a M n : ℕ) (hn : 0 < n) :
    (M : ℝ) * primitiveDensity n - (2 : ℝ) ^ (oddPrimeFactors n).card ≤
      (((Finset.Ico a (a + M)).filter (fun k => (2 * k + 1).Coprime n)).card : ℝ) := by
  have h := (abs_le.mp (primitive_count_error a M n hn)).1
  linarith

end Erdos1151
