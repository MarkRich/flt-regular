import BealRegular.TwentyThreeBernoulli

/-!
# Bernoulli numerators as p-adic units

This file converts the finite Bernoulli-numerator condition used by Kummer's
criterion into an equivalent valuation statement.  The denominator control is
proved from the von Staudt--Clausen theorem, and the existing certificate at
`23` then supplies the corresponding p-adic-unit condition unconditionally.
-/

@[expose] public section

open Nat Finset

namespace BealRegular.KummerBernoulliBridge

open BealRegular.TwentyThreeBernoulli

/-- A prime outside the von Staudt correction set does not divide the
denominator of the corresponding even Bernoulli number. -/
theorem prime_not_dvd_bernoulli_den_of_not_dvd_sub_one
    {p k : ℕ} [Fact p.Prime]
    (hnot : ¬ (p - 1) ∣ 2 * k) :
    ¬ p ∣ (bernoulli (2 * k)).den := by
  let S := (range (2 * k + 2)).filter fun q ↦ q.Prime ∧ (q - 1) ∣ 2 * k
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  change (z : ℚ) = bernoulli (2 * k) + ∑ q ∈ S, (1 : ℚ) / q at hz
  have hB : bernoulli (2 * k) = (z : ℚ) - ∑ q ∈ S, (1 : ℚ) / q :=
    eq_sub_of_add_eq hz.symm
  have hprod :
      (∏ q ∈ S, ((1 : ℚ) / q).den).Coprime p := by
    apply Nat.Coprime.prod_left
    intro q hq
    simp only [S, mem_filter, mem_range] at hq
    have hqp : q ≠ p := by
      intro heq
      exact hnot (heq ▸ hq.2.2)
    rw [show ((1 : ℚ) / q).den = q by simp [hq.2.1.ne_zero]]
    exact (Nat.coprime_primes hq.2.1 (Fact.out : p.Prime)).mpr hqp
  have hsum :
      (∑ q ∈ S, (1 : ℚ) / q).den.Coprime p :=
    Nat.Coprime.of_dvd_left
      (Finset.Rat.den_sum_dvd_prod_den S fun q ↦ (1 : ℚ) / q) hprod
  apply ((Fact.out : p.Prime).coprime_iff_not_dvd).mp
  rw [hB]
  exact (Nat.Coprime.of_dvd_left (Rat.sub_den_dvd (z : ℚ)
    (∑ q ∈ S, (1 : ℚ) / q)) (by simpa using hsum)).symm

/-- Every Bernoulli number occurring in Kummer's finite range is
`p`-integral; the condition on its reduced numerator therefore really is a
nonvanishing condition modulo `p`. -/
theorem prime_not_dvd_bernoulli_den_in_kummer_range
    {p k : ℕ} [Fact p.Prime]
    (hk : 1 ≤ k) (htop : 2 * k ≤ p - 3) :
    ¬ p ∣ (bernoulli (2 * k)).den := by
  apply prime_not_dvd_bernoulli_den_of_not_dvd_sub_one
  intro hdvd
  have hpos : 0 < 2 * k := by omega
  have hle : p - 1 ≤ 2 * k := Nat.le_of_dvd hpos hdvd
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

/-- For a `p`-integral rational, nondivisibility of the reduced numerator is
equivalent to having multiplicative `p`-adic valuation one. -/
theorem rat_padicValuation_eq_one_iff_not_dvd_num
    {p : ℕ} [Fact p.Prime] {x : ℚ} (hden : ¬ p ∣ x.den) :
    Rat.padicValuation p x = 1 ↔ ¬ (p : ℤ) ∣ x.num := by
  conv_lhs => rw [← x.num_div_den, map_div₀, Rat.padicValuation_cast,
    ← Int.cast_natCast, Rat.padicValuation_cast]
  have hden' : ¬ (p : ℤ) ∣ (x.den : ℤ) := by
    exact_mod_cast hden
  rw [Int.padicValuation_eq_one_iff.mpr hden', div_one,
    Int.padicValuation_eq_one_iff]

/-- In Kummer's range, the reduced-numerator condition is exactly a statement
that the Bernoulli number is a `p`-adic unit. -/
theorem bernoulli_padicValuation_eq_one_iff_not_dvd_num
    {p k : ℕ} [Fact p.Prime]
    (hk : 1 ≤ k) (htop : 2 * k ≤ p - 3) :
    Rat.padicValuation p (bernoulli (2 * k)) = 1 ↔
      ¬ (p : ℤ) ∣ (bernoulli (2 * k)).num :=
  rat_padicValuation_eq_one_iff_not_dvd_num
    (prime_not_dvd_bernoulli_den_in_kummer_range hk htop)

/-- The valuation-theoretic form of the finite Bernoulli condition. This is
the form consumed by the usual character/eigenspace proof of Kummer's
criterion. -/
def BernoulliPadicUnitCondition (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ k : ℕ, 1 ≤ k → 2 * k ≤ p - 3 →
    Rat.padicValuation p (bernoulli (2 * k)) = 1

theorem bernoulliNumeratorCondition_iff_padicUnitCondition
    (p : ℕ) [Fact p.Prime] :
    BernoulliNumeratorCondition p ↔ BernoulliPadicUnitCondition p := by
  constructor
  · intro h k hk htop
    exact (bernoulli_padicValuation_eq_one_iff_not_dvd_num hk htop).2
      (h k hk htop)
  · intro h k hk htop
    exact (bernoulli_padicValuation_eq_one_iff_not_dvd_num hk htop).1
      (h k hk htop)

/-- Unconditional valuation-form certificate for the prime `23`. -/
theorem twentyThree_bernoulliPadicUnitCondition :
    @BernoulliPadicUnitCondition 23 ⟨by norm_num⟩ := by
  letI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  exact (bernoulliNumeratorCondition_iff_padicUnitCondition 23).1
    twentyThree_bernoulliNumeratorCondition

end BealRegular.KummerBernoulliBridge
