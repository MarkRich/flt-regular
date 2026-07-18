import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The forward local valuation profile for signature `(3,5,7)`

For the paper orientation `x^5 + y^3 = z^7`, this file uses the variable map
`x = B`, `y = A`, and `z = C`.  Thus

`eta = B^5 / C^7`

and the equation `A^3 + B^5 = C^7` gives `1 - eta = A^3 / C^7`.
Only this forward implication is formalized; no converse is stated.

Mathlib defines `padicValRat p 0 = 0`, so every quotient valuation theorem
below carries the nonzero hypotheses needed for the usual subtraction law.
-/

namespace BealRegular.Signature357LocalRatio

/-- The rational local ratio corresponding to the paper's `eta = x^5/z^7`,
under the variable map `x = B`, `y = A`, `z = C`. -/
def eta (B C : ℕ) : ℚ := (B : ℚ) ^ 5 / (C : ℚ) ^ 7

/-- The signature equation identifies the complementary ratio `1 - eta`. -/
theorem one_sub_eta_eq {A B C : ℕ} (hC : C ≠ 0)
    (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    1 - eta B C = (A : ℚ) ^ 3 / (C : ℚ) ^ 7 := by
  have hCq : (C : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hC
  have hCpow : (C : ℚ) ^ 7 ≠ 0 := pow_ne_zero 7 hCq
  have hEqQ : (A : ℚ) ^ 3 + (B : ℚ) ^ 5 = (C : ℚ) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ ↦ (n : ℚ)) hEq
  rw [eta]
  calc
    1 - (B : ℚ) ^ 5 / (C : ℚ) ^ 7 =
        (C : ℚ) ^ 7 / (C : ℚ) ^ 7 -
          (B : ℚ) ^ 5 / (C : ℚ) ^ 7 := by rw [div_self hCpow]
    _ = ((C : ℚ) ^ 7 - (B : ℚ) ^ 5) / (C : ℚ) ^ 7 := by
      rw [sub_div]
    _ = (A : ℚ) ^ 3 / (C : ℚ) ^ 7 := by
      rw [← eq_sub_of_add_eq hEqQ]

/-- The valuation of `eta` is the expected numerator valuation minus the
denominator valuation. -/
theorem padicValRat_eta {p B C : ℕ} (hp : p.Prime)
    (hB : B ≠ 0) (hC : C ≠ 0) :
    padicValRat p (eta B C) =
      5 * (padicValNat p B : ℤ) - 7 * (padicValNat p C : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hBq : (B : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB
  have hCq : (C : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hC
  rw [eta, padicValRat.div (pow_ne_zero 5 hBq) (pow_ne_zero 7 hCq),
    padicValRat.pow, padicValRat.pow]
  simp only [padicValRat.of_nat]
  norm_num

/-- The equation gives the corresponding valuation formula for `1 - eta`. -/
theorem padicValRat_one_sub_eta {p A B C : ℕ} (hp : p.Prime)
    (hA : A ≠ 0) (hC : C ≠ 0)
    (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    padicValRat p (1 - eta B C) =
      3 * (padicValNat p A : ℤ) - 7 * (padicValNat p C : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hAq : (A : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hA
  have hCq : (C : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hC
  rw [one_sub_eta_eq hC hEq,
    padicValRat.div (pow_ne_zero 3 hAq) (pow_ne_zero 7 hCq),
    padicValRat.pow, padicValRat.pow]
  simp only [padicValRat.of_nat]
  norm_num

private theorem not_prime_dvd_right_of_coprime_of_dvd_left
    {p x y : ℕ} (hp : p.Prime) (hxy : Nat.Coprime x y)
    (hx : p ∣ x) : ¬p ∣ y := by
  have hpy : Nat.Coprime p y := Nat.Coprime.of_dvd_left hx hxy
  exact hp.coprime_iff_not_dvd.mp hpy

/-- Forward local valuation profile for `eta = B^5/C^7`.

For every prime `p`, the valuation pair `(v_p(eta), v_p(1-eta))` is one of

* `(0, 0)`;
* `(5k, 0)` for some positive `k` (the paper's `p ∣ x`, here `p ∣ B` case);
* `(0, 3k)` for some positive `k` (the paper's `p ∣ y`, here `p ∣ A` case);
* `(-7k, -7k)` for some positive `k` (the paper's `p ∣ z`, here `p ∣ C` case).

This is derived from the equation and pairwise coprimality.  It does not state
or prove a converse from a valuation pair back to a Diophantine solution. -/
theorem signature357_localRatio_valuation_profile {p A B C : ℕ}
    (hp : p.Prime)
    (hApos : 0 < A) (hBpos : 0 < B) (hCpos : 0 < C)
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (hBC : Nat.Coprime B C)
    (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    (padicValRat p (eta B C) = 0 ∧
      padicValRat p (1 - eta B C) = 0) ∨
    (∃ k : ℕ, 0 < k ∧
      padicValRat p (eta B C) = 5 * (k : ℤ) ∧
      padicValRat p (1 - eta B C) = 0) ∨
    (∃ k : ℕ, 0 < k ∧
      padicValRat p (eta B C) = 0 ∧
      padicValRat p (1 - eta B C) = 3 * (k : ℤ)) ∨
    (∃ k : ℕ, 0 < k ∧
      padicValRat p (eta B C) = -(7 * (k : ℤ)) ∧
      padicValRat p (1 - eta B C) = -(7 * (k : ℤ))) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hA0 : A ≠ 0 := Nat.ne_of_gt hApos
  have hB0 : B ≠ 0 := Nat.ne_of_gt hBpos
  have hC0 : C ≠ 0 := Nat.ne_of_gt hCpos
  have hEta := padicValRat_eta hp hB0 hC0
  have hOne := padicValRat_one_sub_eta hp hA0 hC0 hEq
  by_cases hpB : p ∣ B
  · have hpA : ¬p ∣ A :=
      not_prime_dvd_right_of_coprime_of_dvd_left hp hAB.symm hpB
    have hpC : ¬p ∣ C :=
      not_prime_dvd_right_of_coprime_of_dvd_left hp hBC hpB
    have hvA : padicValNat p A = 0 :=
      padicValNat.eq_zero_of_not_dvd hpA
    have hvC : padicValNat p C = 0 :=
      padicValNat.eq_zero_of_not_dvd hpC
    have hvBne : padicValNat p B ≠ 0 :=
      (dvd_iff_padicValNat_ne_zero hB0).mp hpB
    refine Or.inr (Or.inl ⟨padicValNat p B, Nat.pos_of_ne_zero hvBne,
      ?_, ?_⟩)
    · simpa only [hvC, Nat.cast_zero, mul_zero, sub_zero] using hEta
    · simpa only [hvA, hvC, Nat.cast_zero, mul_zero, sub_self] using hOne
  · by_cases hpA : p ∣ A
    · have hpC : ¬p ∣ C :=
        not_prime_dvd_right_of_coprime_of_dvd_left hp hAC hpA
      have hvB : padicValNat p B = 0 :=
        padicValNat.eq_zero_of_not_dvd hpB
      have hvC : padicValNat p C = 0 :=
        padicValNat.eq_zero_of_not_dvd hpC
      have hvAne : padicValNat p A ≠ 0 :=
        (dvd_iff_padicValNat_ne_zero hA0).mp hpA
      refine Or.inr (Or.inr (Or.inl ⟨padicValNat p A,
        Nat.pos_of_ne_zero hvAne, ?_, ?_⟩))
      · simpa only [hvB, hvC, Nat.cast_zero, mul_zero, sub_self] using hEta
      · simpa only [hvC, Nat.cast_zero, mul_zero, sub_zero] using hOne
    · by_cases hpC : p ∣ C
      · have hvA : padicValNat p A = 0 :=
          padicValNat.eq_zero_of_not_dvd hpA
        have hvB : padicValNat p B = 0 :=
          padicValNat.eq_zero_of_not_dvd hpB
        have hvCne : padicValNat p C ≠ 0 :=
          (dvd_iff_padicValNat_ne_zero hC0).mp hpC
        refine Or.inr (Or.inr (Or.inr ⟨padicValNat p C,
          Nat.pos_of_ne_zero hvCne, ?_, ?_⟩))
        · simpa only [hvB, Nat.cast_zero, mul_zero, zero_sub] using hEta
        · simpa only [hvA, Nat.cast_zero, mul_zero, zero_sub] using hOne
      · have hvA : padicValNat p A = 0 :=
          padicValNat.eq_zero_of_not_dvd hpA
        have hvB : padicValNat p B = 0 :=
          padicValNat.eq_zero_of_not_dvd hpB
        have hvC : padicValNat p C = 0 :=
          padicValNat.eq_zero_of_not_dvd hpC
        exact Or.inl ⟨
          by simpa only [hvB, hvC, Nat.cast_zero, mul_zero, sub_self] using hEta,
          by simpa only [hvA, hvC, Nat.cast_zero, mul_zero, sub_self] using hOne⟩

end BealRegular.Signature357LocalRatio
