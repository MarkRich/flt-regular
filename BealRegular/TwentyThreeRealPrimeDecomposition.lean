import BealRegular.TwentyThreeLocalEulerFactors
import BealRegular.TwentyThreeRealSubfieldPrimeClassification
import BealRegular.TwentyThreeRealSubfieldClassNumber

/-!
# Prime decomposition in the maximal real subfield at 23

This file classifies the inertia degree, ramification index, and number of
primes above every rational prime away from `23` in the maximal real subfield
of `ℚ(ζ₂₃)`.  The result is indexed by the order of the rational prime modulo
`23`: orders `1` and `2` split into eleven degree-one primes, while orders
`11` and `22` give one degree-eleven prime.

These are finite-prime decomposition theorems.  They do not by themselves
construct a Dedekind-zeta Euler product or a global zeta factorization.
-/

open scoped BigOperators NumberField

namespace BealRegular.TwentyThreeRealPrimeDecomposition

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open IsDedekindDomain

noncomputable section

local notation "K23" => CyclotomicField 23 ℚ
local notation "K23plus" => NumberField.maximalRealSubfield K23

local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

local instance : IsCyclotomicExtension {23} ℚ K23 :=
  CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero 23 ℚ

local instance : IsAbelianGalois ℚ K23 :=
  IsCyclotomicExtension.isAbelianGalois {23} ℚ K23

local instance : IsGalois ℚ K23plus :=
  BealRegular.TwentyThreeRealSubfieldClassNumber.maximalRealSubfield_isGalois

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

/-- In the maximal real subfield, the inertia degree at a rational prime
`q ≠ 23` is `1` for orders `1` and `2`, and `11` for orders `11` and `22`. -/
theorem realSubfield_inertiaDeg_order_cases
    {q : ℕ} (hq : Nat.Prime q) (hq23 : q ≠ 23)
    (P : Ideal.primesOver (Ideal.span {(q : ℤ)})
      (NumberField.RingOfIntegers K23plus)) :
    (orderOf (q : ZMod 23) = 1 ∧
        (P : Ideal (NumberField.RingOfIntegers K23plus)).inertiaDeg ℤ = 1) ∨
    (orderOf (q : ZMod 23) = 2 ∧
        (P : Ideal (NumberField.RingOfIntegers K23plus)).inertiaDeg ℤ = 1) ∨
    (orderOf (q : ZMod 23) = 11 ∧
        (P : Ideal (NumberField.RingOfIntegers K23plus)).inertiaDeg ℤ = 11) ∨
    (orderOf (q : ZMod 23) = 22 ∧
        (P : Ideal (NumberField.RingOfIntegers K23plus)).inertiaDeg ℤ = 11) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let p : Ideal ℤ := Ideal.span {(q : ℤ)}
  let P' : Ideal (NumberField.RingOfIntegers K23plus) := P
  have hpne : p ≠ ⊥ := by
    change Ideal.span {(q : ℤ)} ≠ ⊥
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Int.ofNat_ne_zero.mpr hq.ne_zero
  have hPprime : P'.IsPrime := P.property.1
  have hPne : P' ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hpne P.property
  letI : p.IsPrime := by
    change (Ideal.span {(q : ℤ)}).IsPrime
    rw [Ideal.span_singleton_prime]
    · exact Nat.prime_iff_prime_int.mp hq
    · exact_mod_cast hq.ne_zero
  letI : P'.IsPrime := hPprime
  letI : P'.IsMaximal := hPprime.isMaximal hPne
  have hPover : P'.LiesOver p := by simpa [p, P'] using P.property.2
  letI : P'.LiesOver p := hPover
  obtain ⟨Q, hQmax, hQoverP⟩ :=
    exists_maximal_ideal_liesOver_of_isIntegral
      (S := NumberField.RingOfIntegers K23) P'
  letI : Q.IsMaximal := hQmax
  letI : Q.LiesOver P' := hQoverP
  have hQoverZ : Q.LiesOver p := LiesOver.trans Q P' p
  letI : Q.LiesOver p := hQoverZ
  have hnot : ¬ q ∣ 23 := by
    intro hdvd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 23)).mp hdvd with hq1 | hqeq
    · exact hq.ne_one hq1
    · exact hq23 hqeq
  have hfull : Q.inertiaDeg ℤ = orderOf (q : ZMod 23) := by
    simpa [p] using
      (IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd q K23 Q hnot)
  have htower :
      Q.inertiaDeg ℤ = P'.inertiaDeg ℤ *
        Q.inertiaDeg (NumberField.RingOfIntegers K23plus) :=
    inertiaDeg_tower P' Q
  have hrelativePos :
      0 < Q.inertiaDeg (NumberField.RingOfIntegers K23plus) :=
    inertiaDeg_pos Q (NumberField.RingOfIntegers K23plus)
  have hrelativeLe :
      Q.inertiaDeg (NumberField.RingOfIntegers K23plus) ≤ 2 := by
    have h := Ideal.inertiaDeg_le_finrank
      (R := NumberField.RingOfIntegers K23plus)
      (S := NumberField.RingOfIntegers K23)
      (p := P') K23plus K23 Q hPne
    rw [Ideal.inertiaDeg'_algebraMap,
      ← Ideal.inertiaDeg_eq_of_isMaximal P' Q,
      Algebra.IsQuadraticExtension.finrank_eq_two K23plus K23] at h
    exact h
  have hfund :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      p (NumberField.RingOfIntegers K23plus) Gal(K23plus/ℚ)
  have hfinrank : Module.finrank ℚ K23plus = 11 :=
    BealRegular.TwentyThreeRealSubfield.maximalRealSubfield_finrank
  rw [IsGalois.card_aut_eq_finrank ℚ K23plus, hfinrank,
    Ideal.inertiaDegIn_eq_inertiaDeg p P' Gal(K23plus/ℚ)] at hfund
  have hPdvd : P'.inertiaDeg ℤ ∣ 11 := by
    refine ⟨(Ideal.primesOver p (NumberField.RingOfIntegers K23plus)).ncard *
      p.ramificationIdxIn (NumberField.RingOfIntegers K23plus), ?_⟩
    calc
      11 = (Ideal.primesOver p
            (NumberField.RingOfIntegers K23plus)).ncard *
              (p.ramificationIdxIn
                (NumberField.RingOfIntegers K23plus) * P'.inertiaDeg ℤ) :=
          hfund.symm
      _ = P'.inertiaDeg ℤ *
          ((Ideal.primesOver p
            (NumberField.RingOfIntegers K23plus)).ncard *
              p.ramificationIdxIn
                (NumberField.RingOfIntegers K23plus)) := by ac_rfl
  have hPpos : 0 < P'.inertiaDeg ℤ := inertiaDeg_pos P' ℤ
  have hPcases : P'.inertiaDeg ℤ = 1 ∨ P'.inertiaDeg ℤ = 11 := by
    rcases Nat.dvd_prime (by decide : Nat.Prime 11) |>.mp hPdvd with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hq0 : (q : ZMod 23) ≠ 0 := by
    intro hzero
    have h23dvdq : 23 ∣ q := (ZMod.natCast_eq_zero_iff q 23).mp hzero
    rcases (Nat.dvd_prime hq).mp h23dvdq with h23one | h23q
    · norm_num at h23one
    · exact hq23 h23q.symm
  let hqUnit : IsUnit (q : ZMod 23) := isUnit_iff_ne_zero.mpr hq0
  let u : (ZMod 23)ˣ := hqUnit.unit
  have hu_spec : (u : ZMod 23) = q := hqUnit.unit_spec
  have horderCases := BealRegular.orderOf_unit_zmodTwentyThree_cases u
  rw [← orderOf_units] at horderCases
  have horderCases' :
      orderOf (q : ZMod 23) = 1 ∨ orderOf (q : ZMod 23) = 2 ∨
        orderOf (q : ZMod 23) = 11 ∨ orderOf (q : ZMod 23) = 22 := by
    simpa only [hu_spec] using horderCases
  rcases hPcases with hP1 | hP11
  · rcases horderCases' with h1 | h2 | h11 | h22
    · exact Or.inl ⟨h1, by simpa [P'] using hP1⟩
    · exact Or.inr (Or.inl ⟨h2, by simpa [P'] using hP1⟩)
    · rw [h11] at hfull
      rw [hP1, one_mul] at htower
      omega
    · rw [h22] at hfull
      rw [hP1, one_mul] at htower
      omega
  · rcases horderCases' with h1 | h2 | h11 | h22
    · rw [h1] at hfull
      rw [hP11] at htower
      omega
    · rw [h2] at hfull
      rw [hP11] at htower
      omega
    · exact Or.inr (Or.inr (Or.inl
        ⟨h11, by simpa [P'] using hP11⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨h22, by simpa [P'] using hP11⟩))

/-- Every rational prime away from `23` is unramified in the maximal real
subfield. -/
theorem realSubfield_ramificationIdx_eq_one
    {q : ℕ} (hq : Nat.Prime q) (hq23 : q ≠ 23)
    (P : Ideal.primesOver (Ideal.span {(q : ℤ)})
      (NumberField.RingOfIntegers K23plus)) :
    (P : Ideal (NumberField.RingOfIntegers K23plus)).ramificationIdx ℤ = 1 := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let p : Ideal ℤ := Ideal.span {(q : ℤ)}
  let P' : Ideal (NumberField.RingOfIntegers K23plus) := P
  have hpne : p ≠ ⊥ := by
    change Ideal.span {(q : ℤ)} ≠ ⊥
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Int.ofNat_ne_zero.mpr hq.ne_zero
  have hPprime : P'.IsPrime := P.property.1
  have hPne : P' ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hpne P.property
  letI : p.IsPrime := by
    change (Ideal.span {(q : ℤ)}).IsPrime
    rw [Ideal.span_singleton_prime]
    · exact Nat.prime_iff_prime_int.mp hq
    · exact_mod_cast hq.ne_zero
  letI : P'.IsPrime := hPprime
  letI : P'.IsMaximal := hPprime.isMaximal hPne
  have hPover : P'.LiesOver p := by simpa [p, P'] using P.property.2
  letI : P'.LiesOver p := hPover
  obtain ⟨Q, hQmax, hQoverP⟩ :=
    exists_maximal_ideal_liesOver_of_isIntegral
      (S := NumberField.RingOfIntegers K23) P'
  letI : Q.IsMaximal := hQmax
  letI : Q.LiesOver P' := hQoverP
  have hQoverZ : Q.LiesOver p := LiesOver.trans Q P' p
  letI : Q.LiesOver p := hQoverZ
  have hnot : ¬ q ∣ 23 := by
    intro hdvd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 23)).mp hdvd with hq1 | hqeq
    · exact hq.ne_one hq1
    · exact hq23 hqeq
  have hfull : Q.ramificationIdx ℤ = 1 := by
    simpa [p] using
      (IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd q K23 Q hnot)
  have hdvd : P'.ramificationIdx ℤ ∣ Q.ramificationIdx ℤ :=
    P'.ramificationIdx_below_dvd Q
  rw [hfull] at hdvd
  have hPone : P'.ramificationIdx ℤ = 1 := Nat.eq_one_of_dvd_one hdvd
  simpa [P'] using hPone

/-- The number of primes in the maximal real subfield is `11` in the split
cases and `1` in the degree-eleven cases. -/
theorem realSubfield_ncard_primesOver_order_cases
    {q : ℕ} (hq : Nat.Prime q) (hq23 : q ≠ 23) :
    (orderOf (q : ZMod 23) = 1 ∧
        (Ideal.primesOver (Ideal.span {(q : ℤ)})
          (NumberField.RingOfIntegers K23plus)).ncard = 11) ∨
    (orderOf (q : ZMod 23) = 2 ∧
        (Ideal.primesOver (Ideal.span {(q : ℤ)})
          (NumberField.RingOfIntegers K23plus)).ncard = 11) ∨
    (orderOf (q : ZMod 23) = 11 ∧
        (Ideal.primesOver (Ideal.span {(q : ℤ)})
          (NumberField.RingOfIntegers K23plus)).ncard = 1) ∨
    (orderOf (q : ZMod 23) = 22 ∧
        (Ideal.primesOver (Ideal.span {(q : ℤ)})
          (NumberField.RingOfIntegers K23plus)).ncard = 1) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let p : Ideal ℤ := Ideal.span {(q : ℤ)}
  have hpne : p ≠ ⊥ := by
    change Ideal.span {(q : ℤ)} ≠ ⊥
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Int.ofNat_ne_zero.mpr hq.ne_zero
  letI : p.IsPrime := by
    change (Ideal.span {(q : ℤ)}).IsPrime
    rw [Ideal.span_singleton_prime]
    · exact Nat.prime_iff_prime_int.mp hq
    · exact_mod_cast hq.ne_zero
  obtain ⟨P⟩ :=
    (inferInstance : Nonempty
      (Ideal.primesOver p (NumberField.RingOfIntegers K23plus)))
  have hPcases := realSubfield_inertiaDeg_order_cases hq hq23 P
  have hram := realSubfield_ramificationIdx_eq_one hq hq23 P
  have hfund :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      p (NumberField.RingOfIntegers K23plus) Gal(K23plus/ℚ)
  have hfinrank : Module.finrank ℚ K23plus = 11 :=
    BealRegular.TwentyThreeRealSubfield.maximalRealSubfield_finrank
  rw [IsGalois.card_aut_eq_finrank ℚ K23plus, hfinrank,
    Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(K23plus/ℚ),
    Ideal.inertiaDegIn_eq_inertiaDeg p P Gal(K23plus/ℚ)] at hfund
  rcases hPcases with h1 | h2 | h11 | h22
  · refine Or.inl ⟨h1.1, ?_⟩
    rw [hram, h1.2] at hfund
    simpa [p] using hfund
  · refine Or.inr (Or.inl ⟨h2.1, ?_⟩)
    rw [hram, h2.2] at hfund
    simpa [p] using hfund
  · refine Or.inr (Or.inr (Or.inl ⟨h11.1, ?_⟩))
    rw [hram, h11.2] at hfund
    simpa [p] using hfund
  · refine Or.inr (Or.inr (Or.inr ⟨h22.1, ?_⟩))
    rw [hram, h22.2] at hfund
    simpa [p] using hfund

end

end BealRegular.TwentyThreeRealPrimeDecomposition
