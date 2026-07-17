import BealRegular.BernoulliPadicUnit
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Regular primes and class-group p-torsion

This file expresses regularity as the absence of nontrivial ideal classes
killed by the `p`-th power map.  It then isolates the remaining
Stickelberger/Herbrand input in Kummer's criterion as one explicit
Bernoulli-unit-to-torsion implication.
-/

@[expose] public section

open Nat NumberField
open scoped NumberField

namespace BealRegular.KummerBernoulliBridge

noncomputable section

/-- A prime is regular exactly when its cyclotomic class group has no
nontrivial element killed by the `p`-th power map. -/
theorem isRegularPrime_iff_no_p_torsion (p : ℕ) [Fact p.Prime] :
    IsRegularPrime p ↔
      ∀ c : ClassGroup (NumberField.RingOfIntegers (CyclotomicField p ℚ)),
        c ^ p = 1 → c = 1 := by
  rw [IsRegularPrime, IsRegularNumber]
  constructor
  · intro hcop c hcpow
    have horder_p : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcpow
    have horder_card : orderOf c ∣
        Fintype.card (ClassGroup
          (NumberField.RingOfIntegers (CyclotomicField p ℚ))) := orderOf_dvd_card
    have horder_one : orderOf c ∣ 1 :=
      (Nat.dvd_gcd horder_p horder_card).trans (by rw [hcop.gcd_eq_one])
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp horder_one)
  · intro htorsion
    rw [(Fact.out : p.Prime).coprime_iff_not_dvd]
    intro hp_card
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card p hp_card
    have hcpow : c ^ p = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by simp [hc])
    have hc_one := htorsion c hcpow
    have : orderOf c = 1 := orderOf_eq_one_iff.mpr hc_one
    exact (Fact.out : p.Prime).ne_one (hc.symm.trans this)

/-- Kummer's criterion can be reduced to the statement that its Bernoulli
condition kills all `p`-torsion in the cyclotomic class group. -/
theorem isRegularPrime_of_bernoulli_no_p_torsion
    (p : ℕ) [Fact p.Prime]
    (hBernoulli : BealRegular.TwentyThreeBernoulli.BernoulliNumeratorCondition p)
    (hKummer :
      BealRegular.TwentyThreeBernoulli.BernoulliNumeratorCondition p →
        ∀ c : ClassGroup (NumberField.RingOfIntegers (CyclotomicField p ℚ)),
          c ^ p = 1 → c = 1) :
    IsRegularPrime p :=
  (isRegularPrime_iff_no_p_torsion p).2 (hKummer hBernoulli)

/-- This is the genuinely missing core after removing the elementary
Bernoulli-denominator and finite-group wrappers: `p`-adic-unit Bernoulli
values must rule out `p`-torsion in the cyclotomic class group. -/
def BernoulliPadicUnitsKillClassGroupPTorsion (p : ℕ) [Fact p.Prime] : Prop :=
  BernoulliPadicUnitCondition p →
    ∀ c : ClassGroup (NumberField.RingOfIntegers (CyclotomicField p ℚ)),
      c ^ p = 1 → c = 1

/-- Kummer's Bernoulli implication is equivalent to the isolated
Stickelberger/Herbrand core above. -/
theorem kummerBernoulliImplication_iff_padicUnitsKillClassGroupPTorsion
    (p : ℕ) [Fact p.Prime] :
    BealRegular.TwentyThreeBernoulli.KummerBernoulliImplication p ↔
      BernoulliPadicUnitsKillClassGroupPTorsion p := by
  rw [BealRegular.TwentyThreeBernoulli.KummerBernoulliImplication,
    BernoulliPadicUnitsKillClassGroupPTorsion]
  constructor
  · intro h hpadic
    apply (isRegularPrime_iff_no_p_torsion p).1
    apply h
    exact (bernoulliNumeratorCondition_iff_padicUnitCondition p).2 hpadic
  · intro h hnum
    apply (isRegularPrime_iff_no_p_torsion p).2
    apply h
    exact (bernoulliNumeratorCondition_iff_padicUnitCondition p).1 hnum

end

end BealRegular.KummerBernoulliBridge
