module

public import BealRegular.TwentyThreeRealSubfieldRingOfIntegers
public import BealRegular.TwentyThreeRealSubfieldDiscriminant
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# Finite-prime classification for the real subfield at 23

The integral generator `betaInteger` has Kummer--Dedekind exponent one, so
its shifted degree-eleven minimal polynomial can select a prime above every
rational prime.  Away from residue classes `1` and `-1` modulo `23`, a tower
comparison with the full cyclotomic field forces the selected prime to have
inertia degree `11`.  Consequently its norm already exceeds the exact
Minkowski floor `900`.

The only rational primes at most `900` not discharged by that norm inequality
are recorded in `exceptionalPrimes`.
-/

@[expose] public section

open Ideal NumberField Polynomial RingOfIntegers UniqueFactorizationMonoid
open scoped NumberField

namespace BealRegular.TwentyThreeRealSubfieldPrimeClassification

open BealRegular.TwentyThreeRealSubfieldEisenstein
open BealRegular.TwentyThreeRealSubfieldRingOfIntegers

noncomputable section

local notation "K23" => CyclotomicField 23 ℚ
local notation "K23plus" => NumberField.maximalRealSubfield K23

local instance : IsCyclotomicExtension {23} ℚ K23 :=
  CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero 23 ℚ

local instance : IsAbelianGalois ℚ K23 :=
  IsCyclotomicExtension.isAbelianGalois {23} ℚ K23

local instance : IsAbelianGalois ℚ K23plus :=
  IsAbelianGalois.tower_bot ℚ K23plus K23

local instance : NumberField.IsCMField K23 :=
  BealRegular.TwentyThreeRealSubfield.cyclotomicFieldTwentyThree_isCMField

local instance : NoZeroSMulDivisors
    (NumberField.RingOfIntegers K23plus)
    (NumberField.RingOfIntegers K23) where
  eq_zero_or_eq_zero_of_smul_eq_zero {c x} h := by
    rw [Algebra.smul_def] at h
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h with hc | hx
    · exact Or.inl
        (NumberField.RingOfIntegers.algebraMap.injective K23plus K23 hc)
    · exact Or.inr hx

local instance : Fact (Nat.Prime 23) :=
  ⟨BealRegular.TwentyThreePrimeTwoCube.prime_twentyThree⟩

set_option maxHeartbeats 0 in
-- The exhaustive order classification normalizes all possibilities through `22`.
/-- Outside the two split residue classes, the order of a prime modulo `23`
is one of the two nontrivial possibilities `11` and `22`. -/
theorem order_mod_twentyThree_eq_eleven_or_twentyTwo
    {p : ℕ} [hp : Fact p.Prime] (hp23 : p ≠ 23)
    (hmod1 : p % 23 ≠ 1) (hmod22 : p % 23 ≠ 22) :
    orderOf (p : ZMod 23) = 11 ∨ orderOf (p : ZMod 23) = 22 := by
  have hnotdvd : ¬ 23 ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp.out).mp h with h | h
    · norm_num at h
    · exact hp23 h.symm
  have hcast0 : (p : ZMod 23) ≠ 0 := by
    simpa [ZMod.natCast_eq_zero_iff] using hnotdvd
  have hcast1 : (p : ZMod 23) ≠ 1 := by
    intro h
    apply hmod1
    simpa using (ZMod.natCast_eq_natCast_iff' p 1 23).mp h
  have hcastNeg1 : (p : ZMod 23) ≠ -1 := by
    intro h
    apply hmod22
    have hp22 : (p : ZMod 23) = (22 : ZMod 23) := by
      calc
        (p : ZMod 23) = -1 := h
        _ = (22 : ZMod 23) := by decide +kernel
    simpa using (ZMod.natCast_eq_natCast_iff' p 22 23).mp hp22
  have hdvd : orderOf (p : ZMod 23) ∣ 22 := by
    simpa using ZMod.orderOf_dvd_card_sub_one hcast0
  have hne1 : orderOf (p : ZMod 23) ≠ 1 := by
    simpa [orderOf_eq_one_iff] using hcast1
  have hne2 : orderOf (p : ZMod 23) ≠ 2 := by
    simpa [CharP.orderOf_eq_two_iff 23 (by norm_num)] using hcastNeg1
  have hle : orderOf (p : ZMod 23) ≤ 22 :=
    Nat.le_of_dvd (by norm_num) hdvd
  interval_cases horder : orderOf (p : ZMod 23) <;> norm_num at *

/-- The reduction of the explicit shifted minimal polynomial modulo `p`. -/
def betaPolynomialMod (p : ℕ) : (ZMod p)[X] :=
  shiftedRealSubfieldPolynomial.map (Int.castRingHom (ZMod p))

theorem betaPolynomialMod_monic (p : ℕ) :
    (betaPolynomialMod p).Monic :=
  shiftedRealSubfieldPolynomial_monic.map _

theorem betaPolynomialMod_natDegree (p : ℕ) [Fact p.Prime] :
    (betaPolynomialMod p).natDegree = 11 := by
  rw [betaPolynomialMod,
    shiftedRealSubfieldPolynomial_monic.natDegree_map,
    shiftedRealSubfieldPolynomial_natDegree]

/-- A normalized irreducible factor of the shifted minimal polynomial modulo
`p`.  Its existence follows from the positive degree of that polynomial. -/
noncomputable def betaFactor (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  Classical.choose (UniqueFactorizationMonoid.exists_mem_normalizedFactors
    (betaPolynomialMod_monic p).ne_zero
    (not_isUnit_of_natDegree_pos _ (by
      rw [betaPolynomialMod_natDegree p]
      norm_num)))

theorem betaFactor_mem_normalizedFactors (p : ℕ) [Fact p.Prime] :
  betaFactor p ∈ normalizedFactors (betaPolynomialMod p) :=
  Classical.choose_spec (UniqueFactorizationMonoid.exists_mem_normalizedFactors
    (betaPolynomialMod_monic p).ne_zero
    (not_isUnit_of_natDegree_pos _ (by
      rw [betaPolynomialMod_natDegree p]
      norm_num)))

theorem betaFactor_mem_monicFactorsMod (p : ℕ) [Fact p.Prime] :
    betaFactor p ∈ monicFactorsMod betaInteger p := by
  rw [Multiset.mem_toFinset, minpoly_int_betaInteger]
  exact betaFactor_mem_normalizedFactors p

/-- The prime above `p` selected by the chosen normalized factor of the
shifted minimal polynomial. -/
noncomputable def betaPrime (p : ℕ) [hp : Fact p.Prime] :
    primesOver (span {(p : ℤ)}) (NumberField.RingOfIntegers K23plus) :=
  (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (show ¬ p ∣ exponent betaInteger by
      rw [betaInteger_exponent]
      exact hp.out.not_dvd_one)).symm
        ⟨betaFactor p, betaFactor_mem_monicFactorsMod p⟩

/-- Kummer--Dedekind identifies the selected prime's inertia degree with the
degree of the chosen polynomial factor. -/
theorem betaPrime_inertiaDeg (p : ℕ) [hp : Fact p.Prime] :
    (betaPrime p : Ideal (NumberField.RingOfIntegers K23plus)).inertiaDeg ℤ =
      (betaFactor p).natDegree := by
  unfold betaPrime
  rw [NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply']

/-- If `p` is neither ramified nor congruent to `1` or `-1` modulo `23`, the
selected real-subfield prime has inertia degree exactly `11`. -/
theorem betaPrime_inertiaDeg_eq_eleven {p : ℕ} [hp : Fact p.Prime]
    (hp23 : p ≠ 23) (hmod1 : p % 23 ≠ 1) (hmod22 : p % 23 ≠ 22) :
    (betaPrime p : Ideal (NumberField.RingOfIntegers K23plus)).inertiaDeg ℤ = 11 := by
  let P : Ideal (NumberField.RingOfIntegers K23plus) := betaPrime p
  have hPprime : P.IsPrime := (betaPrime p).property.1
  have hPne : P ≠ ⊥ := by
    intro hP
    have hover : (span {(p : ℤ)} : Ideal ℤ) = P.under ℤ :=
      (betaPrime p).property.2.over
    rw [hP] at hover
    exact hp.out.ne_zero (by simpa using hover)
  letI : P.IsPrime := hPprime
  letI : P.IsMaximal := hPprime.isMaximal hPne
  obtain ⟨Q, hQmax, hQoverP⟩ :=
    exists_maximal_ideal_liesOver_of_isIntegral
      (S := NumberField.RingOfIntegers K23) P
  letI : Q.IsMaximal := hQmax
  letI : Q.LiesOver P := hQoverP
  have hQoverZ : Q.LiesOver (span {(p : ℤ)}) :=
    LiesOver.trans Q P (span {(p : ℤ)})
  letI : Q.LiesOver (span {(p : ℤ)}) := hQoverZ
  have hnotdvd : ¬ p ∣ 23 := by
    intro h
    rcases (Nat.dvd_prime
      BealRegular.TwentyThreePrimeTwoCube.prime_twentyThree).mp h with h | h
    · exact hp.out.ne_one h
    · exact hp23 h
  have hfull : Q.inertiaDeg ℤ = orderOf (p : ZMod 23) :=
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p K23 Q hnotdvd
  have htower :
      Q.inertiaDeg ℤ = P.inertiaDeg ℤ *
        Q.inertiaDeg (NumberField.RingOfIntegers K23plus) :=
    inertiaDeg_tower P Q
  have hrelative :
      Q.inertiaDeg (NumberField.RingOfIntegers K23plus) ≤ 2 := by
    have h := Ideal.inertiaDeg_le_finrank
      (R := NumberField.RingOfIntegers K23plus)
      (S := NumberField.RingOfIntegers K23)
      (p := P) K23plus K23 Q hPne
    rw [Ideal.inertiaDeg'_algebraMap,
      ← Ideal.inertiaDeg_eq_of_isMaximal P Q,
      Algebra.IsQuadraticExtension.finrank_eq_two K23plus K23] at h
    exact h
  have hPupper : P.inertiaDeg ℤ ≤ 11 := by
    rw [show P.inertiaDeg ℤ = (betaFactor p).natDegree by
      simpa [P] using betaPrime_inertiaDeg p]
    have hdvd : betaFactor p ∣ betaPolynomialMod p :=
      dvd_of_mem_normalizedFactors (betaFactor_mem_normalizedFactors p)
    exact (natDegree_le_of_dvd hdvd
      (betaPolynomialMod_monic p).ne_zero).trans_eq
        (betaPolynomialMod_natDegree p)
  have hrelativePos :
      0 < Q.inertiaDeg (NumberField.RingOfIntegers K23plus) :=
    inertiaDeg_pos Q (NumberField.RingOfIntegers K23plus)
  have hrelativeCases :
      Q.inertiaDeg (NumberField.RingOfIntegers K23plus) = 1 ∨
        Q.inertiaDeg (NumberField.RingOfIntegers K23plus) = 2 := by
    omega
  have hPexact : P.inertiaDeg ℤ = 11 := by
    rcases order_mod_twentyThree_eq_eleven_or_twentyTwo hp23 hmod1 hmod22 with
      horder | horder
    · rcases hrelativeCases with hrelativeOne | hrelativeTwo
      · rw [horder] at hfull
        rw [hrelativeOne, mul_one] at htower
        omega
      · rw [horder] at hfull
        rw [hrelativeTwo] at htower
        omega
    · rcases hrelativeCases with hrelativeOne | hrelativeTwo
      · rw [horder] at hfull
        rw [hrelativeOne, mul_one] at htower
        omega
      · rw [horder] at hfull
        rw [hrelativeTwo] at htower
        omega
  simpa [P] using hPexact

/-- The rational primes at most `900` whose real-subfield inertia degree does
not make their prime-ideal norm exceed the Minkowski bound. -/
def exceptionalPrimes : Finset ℕ :=
  [23, 47, 137, 139, 229, 277, 367, 461, 599, 643, 691, 827, 829].toFinset

set_option linter.unusedTactic false in
set_option maxHeartbeats 0 in
-- This exhausts the finitely many quotients `p / 23` allowed by `p ≤ 900`.
theorem prime_mem_exceptional_of_mod_eq_one {p : ℕ}
    (hp : p.Prime) (hple : p ≤ 900) (hmod : p % 23 = 1) :
    p ∈ exceptionalPrimes := by
  let k := p / 23
  have hpform : p = 23 * k + 1 := by
    dsimp [k]
    omega
  have hk : k ≤ 39 := by omega
  interval_cases k <;> subst_vars
  all_goals solve
    | norm_num at hp
    | norm_num [exceptionalPrimes]

set_option linter.unusedTactic false in
set_option maxHeartbeats 0 in
-- This exhausts the finitely many quotients `p / 23` allowed by `p ≤ 900`.
theorem prime_mem_exceptional_of_mod_eq_twentyTwo {p : ℕ}
    (hp : p.Prime) (hple : p ≤ 900) (hmod : p % 23 = 22) :
    p ∈ exceptionalPrimes := by
  let k := p / 23
  have hpform : p = 23 * k + 22 := by
    dsimp [k]
    omega
  have hk : k ≤ 38 := by omega
  interval_cases k <;> subst_vars
  all_goals solve
    | norm_num at hp
    | norm_num [exceptionalPrimes]

/-- Every rational prime at most `900` is either in the explicit exceptional
list or the selected prime above it already has norm greater than `900`. -/
theorem prime_mem_exceptional_or_betaPrime_norm_large {p : ℕ}
    [hp : Fact p.Prime] (hple : p ≤ 900) :
    p ∈ exceptionalPrimes ∨
      900 < p ^
        (betaPrime p : Ideal
          (NumberField.RingOfIntegers K23plus)).inertiaDeg ℤ := by
  by_cases hp23 : p = 23
  · left
    subst p
    norm_num [exceptionalPrimes]
  by_cases hmod1 : p % 23 = 1
  · exact Or.inl (prime_mem_exceptional_of_mod_eq_one hp.out hple hmod1)
  by_cases hmod22 : p % 23 = 22
  · exact Or.inl
      (prime_mem_exceptional_of_mod_eq_twentyTwo hp.out hple hmod22)
  right
  rw [betaPrime_inertiaDeg_eq_eleven hp23 hmod1 hmod22]
  calc
    900 < 2 ^ 11 := by norm_num
    _ ≤ p ^ 11 := Nat.pow_le_pow_left hp.out.two_le 11

/-- Existential form of the finite classification, matching the selected-prime
shape consumed by the real-subfield Minkowski criterion. -/
theorem prime_mem_exceptional_or_exists_prime_norm_large {p : ℕ}
    [hp : Fact p.Prime] (hple : p ≤ 900) :
    p ∈ exceptionalPrimes ∨
      ∃ P ∈ primesOver (span {(p : ℤ)})
          (NumberField.RingOfIntegers K23plus),
        900 < p ^ P.inertiaDeg ℤ := by
  rcases prime_mem_exceptional_or_betaPrime_norm_large hple with h | h
  · exact Or.inl h
  · exact Or.inr ⟨betaPrime p, (betaPrime p).property, h⟩

theorem exists_prime_norm_large_of_not_exceptional {p : ℕ}
    [hp : Fact p.Prime] (hple : p ≤ 900) (hnot : p ∉ exceptionalPrimes) :
    ∃ P ∈ primesOver (span {(p : ℤ)})
        (NumberField.RingOfIntegers K23plus),
      900 < p ^ P.inertiaDeg ℤ :=
  (prime_mem_exceptional_or_exists_prime_norm_large hple).resolve_left hnot

end

end BealRegular.TwentyThreeRealSubfieldPrimeClassification
