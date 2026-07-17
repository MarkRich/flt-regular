module

public import BealRegular.TwentyThreeRealCertificates
public import BealRegular.TwentyThreeRealSubfieldClassNumber
public import BealRegular.TwentyThreeRealSubfieldPrimeClassification

/-!
# Class number one for the maximal real subfield at 23

The inertia-degree classifier eliminates every rational prime below the exact
Minkowski bound except thirteen explicit primes.  The ramified prime `23` is
principal by the Eisenstein generator, and the other twelve primes are
discharged by exact polynomial certificates.  This proves that the canonical
ring of integers is a principal ideal ring and that the real subfield has
class number one.
-/

@[expose] public section

open Ideal NumberField

namespace BealRegular.TwentyThreeRealSubfieldPID

open BealRegular.TwentyThreeRealSubfieldClassNumber
open BealRegular.TwentyThreeRealSubfieldPrimeClassification

noncomputable section

local notation "K23" => CyclotomicField 23 ℚ
local notation "K23plus" => NumberField.maximalRealSubfield K23

/-- Every rational prime below the exact Minkowski cutoff has a selected prime
above it whose norm is already too large or which is explicitly principal. -/
theorem one_prime_above_minkowski :
    ∀ (p : ℕ), p ∈ Finset.Icc 1 900 → p.Prime →
      ∃ P ∈ primesOver (span ({(p : ℤ)} : Set ℤ))
          (NumberField.RingOfIntegers K23plus),
        900 < p ^ P.inertiaDeg ℤ ∨ Submodule.IsPrincipal P := by
  intro p hpRange hpPrime
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hpLe : p ≤ 900 := (Finset.mem_Icc.mp hpRange).2
  rcases prime_mem_exceptional_or_exists_prime_norm_large (p := p) hpLe with
    hExceptional | ⟨P, hP, hLarge⟩
  · have hCases :
        p = 23 ∨ p = 47 ∨ p = 137 ∨ p = 139 ∨ p = 229 ∨ p = 277 ∨
          p = 367 ∨ p = 461 ∨ p = 599 ∨ p = 643 ∨ p = 691 ∨
            p = 827 ∨ p = 829 := by
      simpa [exceptionalPrimes] using hExceptional
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_twentyThree_branch
    · exact BealRegular.TwentyThreeRealCertificates.Q47.minkowski_branch
    · exact BealRegular.TwentyThreeRealCertificates.Q137.minkowski_branch
    · exact BealRegular.TwentyThreeRealCertificates.Q139.minkowski_branch
    · exact BealRegular.TwentyThreeRealCertificates.Q229.minkowski_branch
    · exact BealRegular.TwentyThreeRealCertificates.Q277.minkowski_branch
    · exact BealRegular.TwentyThreeRealCertificates.Q367.minkowski_branch
    · exact BealRegular.TwentyThreeRealCertificates.Q461.minkowski_branch
    · exact BealRegular.TwentyThreeRealCertificates.Q599.minkowski_branch
    · exact BealRegular.TwentyThreeRealCertificates.Q643.minkowski_branch
    · exact BealRegular.TwentyThreeRealCertificates.Q691.minkowski_branch
    · exact BealRegular.TwentyThreeRealCertificates.Q827.minkowski_branch
    · exact BealRegular.TwentyThreeRealCertificates.Q829.minkowski_branch
  · exact ⟨P, hP, Or.inl hLarge⟩

/-- The ring of integers of the maximal real subfield of `ℚ(ζ₂₃)` is a
principal ideal ring. -/
theorem ringOfIntegers_isPrincipalIdealRing :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K23plus) :=
  isPrincipalIdealRing_of_one_prime_above one_prime_above_minkowski

/-- The maximal real subfield of the 23rd cyclotomic field has class number
exactly one. -/
theorem maximalRealSubfield_classNumber_eq_one :
    NumberField.classNumber K23plus = 1 :=
  classNumber_eq_one_of_one_prime_above one_prime_above_minkowski

end

end BealRegular.TwentyThreeRealSubfieldPID
