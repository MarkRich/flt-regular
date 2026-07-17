import BealRegular.GaussianQuarticThreeBridge
import Mathlib.NumberTheory.FLT.Four

/-!
# Divisibility closures for fourth-power sums

The completed `(4,4,3)` bridge and the formal exponent-four case of Fermat's
Last Theorem cover two infinite families.  When the result exponent is
divisible by three, its quotient can be absorbed into the result base and the
exact common-prime conclusion descends back to the original base.  When it is
divisible by four, there is no solution with nonzero bases even without
coprimality.
-/

namespace BealRegular.FourthPowerSumDivisibility

open BealRegular.GaussianQuarticThreeBridge
open BealRegular.SignatureReduction

/-- A coprime equation `A^4 + B^4 = C^n` has no nonzero solution when
`3 ∣ n`.  Only coprimality of the two summands is needed. -/
theorem no_coprime_fourthPowerSum_if_three_dvd_exponent
    {A B C n : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hAB : Nat.Coprime A B)
    (hn : 3 ∣ n) :
    A ^ 4 + B ^ 4 ≠ C ^ n := by
  intro hEq
  obtain ⟨k, hk⟩ := hn
  have hEqCube : A ^ 4 + B ^ 4 = (C ^ k) ^ 3 := by
    calc
      A ^ 4 + B ^ 4 = C ^ n := hEq
      _ = C ^ (3 * k) := by rw [hk]
      _ = C ^ (k * 3) := by rw [Nat.mul_comm 3 k]
      _ = (C ^ k) ^ 3 := pow_mul C k 3
  exact no_primitive_four_four_three hA hB hAB hEqCube

/-- Exact Beal conclusion for the infinite family `A^4 + B^4 = C^n` with
`3 ∣ n`: every nonzero solution has a prime common to all three bases. -/
theorem fourthPowerSum_hasCommonPrimeFactor_if_three_dvd_exponent
    {A B C n : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hn : 3 ∣ n) (hEq : A ^ 4 + B ^ 4 = C ^ n) :
    HasCommonPrimeFactor A B C := by
  obtain ⟨k, hk⟩ := hn
  have hEqCube : A ^ 4 + B ^ 4 = (C ^ k) ^ 3 := by
    calc
      A ^ 4 + B ^ 4 = C ^ n := hEq
      _ = C ^ (3 * k) := by rw [hk]
      _ = C ^ (k * 3) := by rw [Nat.mul_comm 3 k]
      _ = (C ^ k) ^ 3 := pow_mul C k 3
  obtain ⟨p, hp, hpA, hpB, hpCk⟩ :=
    four_four_three_hasCommonPrimeFactor hA hB (pow_ne_zero k hC) hEqCube
  exact ⟨p, hp, hpA, hpB, hp.dvd_of_dvd_pow hpCk⟩

/-- An equation `A^4 + B^4 = C^n` with nonzero bases has no solution when
`4 ∣ n`; no coprimality assumption is needed. -/
theorem no_fourthPowerSum_if_four_dvd_exponent
    {A B C n : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hn : 4 ∣ n) :
    A ^ 4 + B ^ 4 ≠ C ^ n := by
  intro hEq
  obtain ⟨k, hk⟩ := hn
  apply fermatLastTheoremFour A B (C ^ k)
    hA hB (pow_ne_zero k hC)
  calc
    A ^ 4 + B ^ 4 = C ^ n := hEq
    _ = C ^ (4 * k) := by rw [hk]
    _ = C ^ (k * 4) := by rw [Nat.mul_comm 4 k]
    _ = (C ^ k) ^ 4 := pow_mul C k 4

/-- Exact Beal conclusion when the result exponent is divisible by three or
four.  The three-divisible branch supplies the common prime; the
four-divisible branch has no solution with nonzero bases. -/
theorem fourthPowerSum_hasCommonPrimeFactor_if_three_or_four_dvd_exponent
    {A B C n : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hn : 3 ∣ n ∨ 4 ∣ n) (hEq : A ^ 4 + B ^ 4 = C ^ n) :
    HasCommonPrimeFactor A B C := by
  rcases hn with hnThree | hnFour
  · exact fourthPowerSum_hasCommonPrimeFactor_if_three_dvd_exponent
      hA hB hC hnThree hEq
  · exact (no_fourthPowerSum_if_four_dvd_exponent hA hB hC hnFour hEq).elim

/-- Coprime nonexistence form of the combined divisibility closure. -/
theorem no_coprime_fourthPowerSum_if_three_or_four_dvd_exponent
    {A B C n : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hAB : Nat.Coprime A B) (hn : 3 ∣ n ∨ 4 ∣ n) :
    A ^ 4 + B ^ 4 ≠ C ^ n := by
  rcases hn with hnThree | hnFour
  · exact no_coprime_fourthPowerSum_if_three_dvd_exponent
      hA hB hAB hnThree
  · exact no_fourthPowerSum_if_four_dvd_exponent hA hB hC hnFour

end BealRegular.FourthPowerSumDivisibility
