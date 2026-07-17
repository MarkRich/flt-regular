module

public import BealRegular.TwentyThreeRealSubfield
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.Tower
public import Mathlib.Tactic.IntervalCases

/-!
# Eisenstein irreducibility for the real-subfield polynomial

Shifting the explicit degree-eleven polynomial by `X ↦ X - 2` produces a
23-Eisenstein polynomial.  This file checks the shift, the Eisenstein
conditions, and transports irreducibility back through the polynomial
translation automorphism.
-/

@[expose] public section

open Ideal Polynomial

namespace BealRegular.TwentyThreeRealSubfieldEisenstein

open BealRegular.TwentyThreeRealSubfield

noncomputable section

local notation "K23" => CyclotomicField 23 ℚ
local notation "K23plus" => NumberField.maximalRealSubfield K23

/-- The exact expansion of `realSubfieldPolynomial (X - 2)`. -/
def shiftedRealSubfieldPolynomial : ℤ[X] :=
  X ^ 11 - C 23 * X ^ 10 + C 230 * X ^ 9 - C 1311 * X ^ 8 +
    C 4692 * X ^ 7 - C 10948 * X ^ 6 + C 16744 * X ^ 5 -
      C 16445 * X ^ 4 + C 9867 * X ^ 3 - C 3289 * X ^ 2 +
        C 506 * X - C 23

theorem shiftedRealSubfieldPolynomial_eq_comp :
    shiftedRealSubfieldPolynomial =
      realSubfieldPolynomial.comp (X - C 2) := by
  simp [shiftedRealSubfieldPolynomial, realSubfieldPolynomial]
  ring

theorem shiftedRealSubfieldPolynomial_monic :
    shiftedRealSubfieldPolynomial.Monic := by
  simp only [shiftedRealSubfieldPolynomial]
  monicity!

theorem shiftedRealSubfieldPolynomial_natDegree :
    shiftedRealSubfieldPolynomial.natDegree = 11 := by
  simp only [shiftedRealSubfieldPolynomial]
  compute_degree!

private theorem primeIdealTwentyThree :
    (span {(23 : ℤ)} : Ideal ℤ).IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).2
    (Nat.prime_iff_prime_int.1
      BealRegular.TwentyThreePrimeTwoCube.prime_twentyThree)

/-- The translated polynomial satisfies Eisenstein's criterion at `23`. -/
theorem shiftedRealSubfieldPolynomial_isEisensteinAt :
    shiftedRealSubfieldPolynomial.IsEisensteinAt
      (span {(23 : ℤ)} : Ideal ℤ) := by
  refine shiftedRealSubfieldPolynomial_monic.isEisensteinAt_of_mem_of_notMem
    primeIdealTwentyThree.ne_top ?_ ?_
  · intro n hn
    rw [shiftedRealSubfieldPolynomial_natDegree] at hn
    interval_cases n <;>
      norm_num [shiftedRealSubfieldPolynomial, Polynomial.coeff_X,
        Ideal.mem_span_singleton]
  · norm_num [shiftedRealSubfieldPolynomial, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]

theorem shiftedRealSubfieldPolynomial_irreducible :
    Irreducible shiftedRealSubfieldPolynomial :=
  shiftedRealSubfieldPolynomial_isEisensteinAt.irreducible
    primeIdealTwentyThree shiftedRealSubfieldPolynomial_monic.isPrimitive
    (by rw [shiftedRealSubfieldPolynomial_natDegree]; norm_num)

theorem realSubfieldPolynomial_monic : realSubfieldPolynomial.Monic := by
  simp only [realSubfieldPolynomial]
  monicity!

theorem realSubfieldPolynomial_natDegree :
    realSubfieldPolynomial.natDegree = 11 := by
  simp only [realSubfieldPolynomial]
  compute_degree!

/-- Translation by `-2` sends the original polynomial to the Eisenstein one. -/
theorem translate_realSubfieldPolynomial :
    Polynomial.algEquivAevalXAddC (-2 : ℤ) realSubfieldPolynomial =
      shiftedRealSubfieldPolynomial := by
  rw [Polynomial.algEquivAevalXAddC_apply, ← Polynomial.comp_eq_aeval]
  rw [show (X + C (-2) : ℤ[X]) = X - C 2 by
    simp [sub_eq_add_neg]]
  exact shiftedRealSubfieldPolynomial_eq_comp.symm

/-- The original integral polynomial is irreducible because polynomial
translation is a multiplicative equivalence. -/
theorem realSubfieldPolynomial_irreducible :
    Irreducible realSubfieldPolynomial := by
  apply (MulEquiv.irreducible_iff
    (Polynomial.algEquivAevalXAddC (-2 : ℤ)).toRingEquiv.toMulEquiv).mp
  change Irreducible
    (Polynomial.algEquivAevalXAddC (-2 : ℤ) realSubfieldPolynomial)
  rw [translate_realSubfieldPolynomial]
  exact shiftedRealSubfieldPolynomial_irreducible

/-- The rational polynomial obtained from the integral model. -/
def realSubfieldPolynomialRat : ℚ[X] :=
  realSubfieldPolynomial.map (Int.castRingHom ℚ)

theorem realSubfieldPolynomialRat_monic :
    realSubfieldPolynomialRat.Monic :=
  realSubfieldPolynomial_monic.map (Int.castRingHom ℚ)

theorem realSubfieldPolynomialRat_irreducible :
    Irreducible realSubfieldPolynomialRat := by
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    realSubfieldPolynomial_monic.isPrimitive).mp
      realSubfieldPolynomial_irreducible

theorem aeval_realSubfieldPolynomialRat_alpha :
    aeval alpha realSubfieldPolynomialRat = 0 := by
  change aeval alpha
    (realSubfieldPolynomial.map (algebraMap ℤ ℚ)) = 0
  rw [Polynomial.aeval_map_algebraMap]
  exact aeval_realSubfieldPolynomial_alpha

/-- The Eisenstein polynomial is exactly the minimal polynomial of `alpha`
over `ℚ`. -/
theorem realSubfieldPolynomialRat_eq_minpoly_alpha :
    realSubfieldPolynomialRat = minpoly ℚ alpha :=
  minpoly.eq_of_irreducible_of_monic
    realSubfieldPolynomialRat_irreducible
    aeval_realSubfieldPolynomialRat_alpha
    realSubfieldPolynomialRat_monic

theorem minpoly_alpha_natDegree :
    (minpoly ℚ alpha).natDegree = 11 := by
  rw [← realSubfieldPolynomialRat_eq_minpoly_alpha,
    realSubfieldPolynomialRat,
    realSubfieldPolynomial_monic.natDegree_map,
    realSubfieldPolynomial_natDegree]

/-- The explicit element `alpha` generates the full maximal real subfield. -/
theorem adjoin_alpha_eq_top :
    IntermediateField.adjoin ℚ ({alpha} : Set K23plus) =
      (⊤ : IntermediateField ℚ K23plus) := by
  have halpha : IsIntegral ℚ alpha :=
    ⟨realSubfieldPolynomialRat, realSubfieldPolynomialRat_monic,
      aeval_realSubfieldPolynomialRat_alpha⟩
  apply IntermediateField.eq_of_le_of_finrank_eq le_top
  rw [IntermediateField.adjoin.finrank halpha, minpoly_alpha_natDegree,
    IntermediateField.finrank_top', maximalRealSubfield_finrank]

end

end BealRegular.TwentyThreeRealSubfieldEisenstein
