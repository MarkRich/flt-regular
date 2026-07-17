import BealRegular.SignatureReduction
import Mathlib.Tactic.NormNum.Prime

/-! Kernel audit and focused examples for coordinatewise Beal reduction. -/

namespace BealRegular.SignatureReduction

#print axioms IsReducedBealExponent
#print axioms HasCommonPrimeFactor
#print axioms BealConjecture
#print axioms ReducedBealConjecture
#print axioms exists_reduced_exponent_factorization
#print axioms IsReducedBealExponent.two_lt
#print axioms hasCommonPrimeFactor_powers_iff
#print axioms hasCommonPrimeFactor_iff_gcd_ne_one
#print axioms gcd_powers_eq_one_iff
#print axioms exists_reduced_generalized_fermat
#print axioms bealConjecture_iff_reducedBealConjecture

/-! The fixed witnesses below exercise every elementary shape used by the
normalization: odd primes, multiples of odd primes, and powers/multiples of
four. -/

example : IsReducedBealExponent 3 ∧ 0 < 1 ∧ 3 = 1 * 3 := by
  refine ⟨Or.inr ⟨by norm_num, by decide⟩, by norm_num, by norm_num⟩

example : IsReducedBealExponent 4 ∧ 0 < 1 ∧ 4 = 1 * 4 := by
  refine ⟨Or.inl rfl, by norm_num, by norm_num⟩

example : IsReducedBealExponent 3 ∧ 0 < 2 ∧ 6 = 2 * 3 := by
  refine ⟨Or.inr ⟨by norm_num, by decide⟩, by norm_num, by norm_num⟩

example : IsReducedBealExponent 4 ∧ 0 < 2 ∧ 8 = 2 * 4 := by
  refine ⟨Or.inl rfl, by norm_num, by norm_num⟩

example : IsReducedBealExponent 5 ∧ 0 < 2 ∧ 10 = 2 * 5 := by
  refine ⟨Or.inr ⟨by norm_num, by decide⟩, by norm_num, by norm_num⟩

example : IsReducedBealExponent 4 ∧ 0 < 3 ∧ 12 = 3 * 4 := by
  refine ⟨Or.inl rfl, by norm_num, by norm_num⟩

/-! `6`, `10`, and `15` are not pairwise coprime, but no one prime divides all
three.  This checks that the formal predicate is Beal's triple condition. -/

example : ¬ HasCommonPrimeFactor 6 10 15 := by
  rw [hasCommonPrimeFactor_iff_gcd_ne_one]
  decide

example :
    Nat.gcd 6 10 ≠ 1 ∧ Nat.gcd 10 15 ≠ 1 ∧ Nat.gcd 6 15 ≠ 1 := by
  decide

end BealRegular.SignatureReduction
