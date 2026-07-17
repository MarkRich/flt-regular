import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Galois action on ideal classes

This file records the functorial action of field automorphisms on the ideal
class group of a number field.  In particular, the action preserves the
subgroup of classes killed by a fixed power.
-/

@[expose] public section

open NumberField
open scoped NumberField

namespace BealRegular.KummerBernoulliBridge

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- A field automorphism restricts to the ring of integers and hence induces
an automorphism of the ideal class group. -/
noncomputable def classGroupAutOfAlgEquiv (σ : K ≃ₐ[ℚ] K) :
    ClassGroup (NumberField.RingOfIntegers K) ≃*
      ClassGroup (NumberField.RingOfIntegers K) :=
  ClassGroup.mulEquiv (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv

@[simp]
theorem classGroupAutOfAlgEquiv_pow (σ : K ≃ₐ[ℚ] K)
    (c : ClassGroup (NumberField.RingOfIntegers K)) (n : ℕ) :
    classGroupAutOfAlgEquiv σ (c ^ n) = (classGroupAutOfAlgEquiv σ c) ^ n := by
  exact map_pow (classGroupAutOfAlgEquiv σ) c n

theorem classGroupAutOfAlgEquiv_preserves_p_torsion (σ : K ≃ₐ[ℚ] K)
    (p : ℕ) (c : ClassGroup (NumberField.RingOfIntegers K)) :
    (classGroupAutOfAlgEquiv σ c) ^ p = 1 ↔ c ^ p = 1 := by
  constructor
  · intro h
    apply (classGroupAutOfAlgEquiv σ).injective
    simpa only [classGroupAutOfAlgEquiv_pow, map_one] using h
  · intro h
    simpa only [classGroupAutOfAlgEquiv_pow, map_one] using
      congrArg (classGroupAutOfAlgEquiv σ) h

end

end BealRegular.KummerBernoulliBridge
