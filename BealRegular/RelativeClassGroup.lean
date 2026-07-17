module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import Mathlib.GroupTheory.Index

/-!
# Quotients by extended ideal classes

For an extension of rings of integers, this file defines the quotient of the
upper class group by ideal classes extended from the base and computes its
cardinality as a subgroup index.

The generic index below is deliberately called `extendedClassIndex`, not a
relative class number: extension of ideal classes need not be injective.  When
the base field has class number one, however, the image is trivial and the
index is exactly the class number of the upper field.
-/

@[expose] public section

open NumberField
open scoped NumberField

namespace BealRegular.RelativeClassGroup

noncomputable section

variable (F K : Type*)
  [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (NumberField.RingOfIntegers F)
    (NumberField.RingOfIntegers K)]
  [Module.IsTorsionFree (NumberField.RingOfIntegers F)
    (NumberField.RingOfIntegers K)]

/-- The upper class group modulo the image of extension from the base field. -/
abbrev ExtendedClassQuotient :=
  ClassGroup (NumberField.RingOfIntegers K) ⧸
    (ClassGroup.extendedHom (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers K)).range

/-- The index of the subgroup of ideal classes extended from the base field.

Without an injectivity theorem for extension on class groups, this should not
be identified with the standard relative class number. -/
def extendedClassIndex : ℕ :=
  (ClassGroup.extendedHom (NumberField.RingOfIntegers F)
    (NumberField.RingOfIntegers K)).range.index

omit [NumberField K] in
/-- If the base field has class number one, every extended ideal class is
trivial. -/
theorem extendedClassGroup_range_eq_bot_of_classNumber_eq_one
    (hF : NumberField.classNumber F = 1) :
    (ClassGroup.extendedHom (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers K)).range = ⊥ := by
  apply le_antisymm
  · intro y hy
    change y = 1
    obtain ⟨x, rfl⟩ := hy
    have hx : x = 1 := by
      obtain ⟨z, hz⟩ := Fintype.card_eq_one_iff.mp hF
      exact (hz x).trans (hz 1).symm
    simp [hx]
  · exact bot_le

/-- Over a class-number-one base, the extended-class index is the full class
number upstairs. -/
theorem extendedClassIndex_eq_classNumber_of_classNumber_eq_one
    (hF : NumberField.classNumber F = 1) :
    extendedClassIndex F K = NumberField.classNumber K := by
  rw [extendedClassIndex,
    extendedClassGroup_range_eq_bot_of_classNumber_eq_one F K hF,
    Subgroup.index_bot, NumberField.classNumber, Nat.card_eq_fintype_card]

omit [NumberField F] [NumberField K] in
/-- The cardinality of the extended-class quotient is its subgroup index. -/
theorem card_extendedClassQuotient_eq_extendedClassIndex :
    Nat.card (ExtendedClassQuotient F K) = extendedClassIndex F K := by
  exact (Subgroup.index_eq_card _).symm

omit [NumberField F] in
/-- The extended-class index times the size of the extended-class image is the
full class number upstairs. -/
theorem extendedClassIndex_mul_card_extendedRange :
    extendedClassIndex F K *
        Nat.card (ClassGroup.extendedHom (NumberField.RingOfIntegers F)
          (NumberField.RingOfIntegers K)).range =
      NumberField.classNumber K := by
  rw [extendedClassIndex, Subgroup.index_mul_card,
    NumberField.classNumber, Nat.card_eq_fintype_card]

end

end BealRegular.RelativeClassGroup
