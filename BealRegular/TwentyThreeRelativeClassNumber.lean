module

public import BealRegular.RelativeClassGroup
public import BealRegular.TwentyThreeRelativeClassNumberResultant
public import BealRegular.TwentyThreeRealSubfieldPID
public import FltRegular.FltRegular

/-!
# The remaining relative class-number formula at 23

The maximal real subfield of `ℚ(ζ₂₃)` has class number one by
`TwentyThreeRealSubfieldPID`.  Consequently, the quotient by classes extended
from that real subfield has cardinality equal to the full cyclotomic class
number.  This lets us use the honest `p = 23` name
`relativeClassNumberTwentyThree` without making a generic injectivity claim.

The finite odd-character resultant has already been computed exactly.  The
only missing mathematical theorem is packaged below as
`RelativeClassNumberFormulaTwentyThree`: it identifies the relative class
number with that normalized finite product.  All consequences in this file
take that proposition as an explicit hypothesis.
-/

@[expose] public section

open NumberField
open scoped NumberField

namespace BealRegular.TwentyThreeRelativeClassNumber

open BealRegular.RelativeClassGroup
open BealRegular.TwentyThreeRelativeClassNumberResultant

noncomputable section

local notation "K23" => CyclotomicField 23 ℚ
local notation "K23plus" => NumberField.maximalRealSubfield K23

local instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩
local instance : IsCyclotomicExtension {23} ℚ K23 :=
  CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero 23 ℚ

/-- At `23`, the index of the classes extended from the maximal real
subfield.  Since that subfield has class number one, this equals the full
cyclotomic class number and hence the usual relative class number. -/
def relativeClassNumberTwentyThree : ℕ :=
  extendedClassIndex K23plus K23

/-- The `p = 23` relative class number is the full cyclotomic class number,
because the maximal real subfield has class number one. -/
theorem relativeClassNumberTwentyThree_eq_classNumber :
    relativeClassNumberTwentyThree = NumberField.classNumber K23 := by
  simpa [relativeClassNumberTwentyThree] using
    extendedClassIndex_eq_classNumber_of_classNumber_eq_one K23plus K23
      BealRegular.TwentyThreeRealSubfieldPID.maximalRealSubfield_classNumber_eq_one

/-- The remaining analytic class-number formula at `23`.

The right-hand side is already kernel-computed to `3`; proving this proposition
requires the missing bridge from the cyclotomic relative class number to the
odd-character product. -/
def RelativeClassNumberFormulaTwentyThree : Prop :=
  (relativeClassNumberTwentyThree : ℚ) =
    -(oddCharacterRootPolynomial.resultant characterSumPolynomial) /
      (46 : ℚ) ^ 10

/-- The missing formula, together with the exact resultant computation, gives
relative class number `3`. -/
theorem relativeClassNumberTwentyThree_eq_three_of_formula
    (hformula : RelativeClassNumberFormulaTwentyThree) :
    relativeClassNumberTwentyThree = 3 := by
  have hq : (relativeClassNumberTwentyThree : ℚ) = 3 :=
    hformula.trans normalizedCharacterSumProduct
  exact_mod_cast hq

/-- The same formula computes the full class number of `ℚ(ζ₂₃)`. -/
theorem cyclotomicClassNumberTwentyThree_eq_three_of_formula
    (hformula : RelativeClassNumberFormulaTwentyThree) :
    NumberField.classNumber K23 = 3 := by
  rw [← relativeClassNumberTwentyThree_eq_classNumber]
  exact relativeClassNumberTwentyThree_eq_three_of_formula hformula

/-- Coprimality of `23` with the `p = 23` relative class number is enough for
regularity; the real-subfield class number has already been discharged. -/
theorem isRegularPrime_twentyThree_of_relativeClassNumber_coprime
    (hrel : Nat.Coprime 23 relativeClassNumberTwentyThree) :
    IsRegularPrime 23 := by
  rw [IsRegularPrime, IsRegularNumber]
  change Nat.Coprime 23 (NumberField.classNumber K23)
  rw [← relativeClassNumberTwentyThree_eq_classNumber]
  exact hrel

/-- The explicit remaining class-number formula implies that `23` is a
regular prime. -/
theorem isRegularPrime_twentyThree_of_relativeClassNumberFormula
    (hformula : RelativeClassNumberFormulaTwentyThree) :
    IsRegularPrime 23 := by
  apply isRegularPrime_twentyThree_of_relativeClassNumber_coprime
  rw [relativeClassNumberTwentyThree_eq_three_of_formula hformula]
  norm_num

/-- The explicit remaining class-number formula implies FLT for exponent
`23`. -/
theorem fermatLastTheoremTwentyThree_of_relativeClassNumberFormula
    (hformula : RelativeClassNumberFormulaTwentyThree) :
    FermatLastTheoremFor 23 :=
  flt_regular
    (isRegularPrime_twentyThree_of_relativeClassNumberFormula hformula)
    (by norm_num)

end

end BealRegular.TwentyThreeRelativeClassNumber
