import BealRegular.SinZetaOne
import BealRegular.TwentyThreeLocalEulerFactors
import BealRegular.TwentyThreeRelativeClassNumberResultant

/-!
# The finite odd-character product at 23

This file connects the eleven analytically continued odd Dirichlet
`L`-values at zero to the exact resultant computed in
`TwentyThreeRelativeClassNumberResultant.lean`.

The residue `5` generates the nonzero classes modulo `23`.  Reindexing by its
twenty-two powers identifies each residue-weighted character sum with the
evaluation of `characterSumPolynomial` at `chi 5`.  The values `chi 5` for the
eleven odd characters are exactly the roots of `X^11 + 1`, so their product of
evaluations is the mapped resultant.  Combining this with the unconditional
odd-character formula from `SinZetaOne.lean` proves

`prod_(chi odd) L(chi, 0) = 3 * 2^10 / 23`.

This is a finite algebraic and special-value calculation.  It does not prove
the global factorization of the cyclotomic Dedekind zeta function by these
Dirichlet `L`-functions.
-/

open scoped BigOperators

open Complex Polynomial

namespace BealRegular.TwentyThreeOddCharacterProduct

noncomputable section

open BealRegular.TwentyThreeRelativeClassNumberResultant

local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

/-- The powers `5^k`, for `0 <= k < 22`, are pairwise distinct modulo `23`. -/
theorem fivePowersTwentyThree_injective :
    Function.Injective (fun k : Fin 22 ↦ (5 : ZMod 23) ^ (k : ℕ)) := by
  decide

/-- Zero together with the twenty-two powers of `5` enumerates all residue
classes modulo `23`. -/
theorem univ_zmodTwentyThree_eq_insert_zero_image_fivePowers :
    (Finset.univ : Finset (ZMod 23)) =
      insert 0 (Finset.univ.image (fun k : Fin 22 ↦ (5 : ZMod 23) ^ (k : ℕ))) := by
  decide

/-- Reindex a residue-weighted character sum by the powers of the primitive
residue `5`. -/
theorem weightedCharacterSum_eq_sum_fivePowers
    (chi : DirichletCharacter ℂ 23) :
    ∑ j : ZMod 23, chi j * (j.val : ℂ) =
      ∑ k : Fin 22,
        chi ((5 : ZMod 23) ^ (k : ℕ)) *
          (((5 : ZMod 23) ^ (k : ℕ)).val : ℂ) := by
  classical
  rw [univ_zmodTwentyThree_eq_insert_zero_image_fivePowers]
  rw [Finset.sum_insert]
  · simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, zero_add]
    rw [Finset.sum_image]
    decide
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro k
    exact pow_ne_zero _ (by decide : (5 : ZMod 23) ≠ 0)

/-- The power-indexed weighted sum is the evaluation of the exact rational
`characterSumPolynomial`. -/
theorem sum_fivePowers_eq_eval_characterSumPolynomial
    (chi : DirichletCharacter ℂ 23) :
    ∑ k : Fin 22,
        chi ((5 : ZMod 23) ^ (k : ℕ)) *
          (((5 : ZMod 23) ^ (k : ℕ)).val : ℂ) =
      Polynomial.eval (chi 5)
        (characterSumPolynomial.map (algebraMap ℚ ℂ)) := by
  simp only [map_pow]
  simp only [ZMod.natCast_val, Fin.sum_univ_succ, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, one_mul, Fin.val_succ,
    zero_add, pow_one, Nat.reduceAdd, Finset.univ_unique, Fin.default_eq_zero,
    Fin.val_eq_zero, Finset.sum_const, Finset.card_singleton, one_smul,
    characterSumPolynomial, map_one, Polynomial.map_add, Polynomial.map_one,
    Polynomial.map_mul, map_C, eq_ratCast, Rat.cast_ofNat, map_X,
    Polynomial.map_pow, eval_add, eval_one, eval_mul, eval_C, eval_X, eval_pow]
  have hcast (k r : ℕ) (h : ((5 : ZMod 23) ^ k).val = r) :
      (ZMod.cast ((5 : ZMod 23) ^ k) : ℂ) = (r : ℂ) := by
    rw [ZMod.cast_eq_val, h]
  have hcastOne : (ZMod.cast (1 : ZMod 23) : ℂ) = 1 := by
    rw [ZMod.cast_eq_val, show (1 : ZMod 23).val = 1 by decide]
    norm_num
  have hcastFive : (ZMod.cast (5 : ZMod 23) : ℂ) = 5 := by
    rw [ZMod.cast_eq_val, show (5 : ZMod 23).val = 5 by decide]
    norm_num
  rw [hcastOne, hcastFive, hcast 2 2 (by decide), hcast 3 10 (by decide),
    hcast 4 4 (by decide), hcast 5 20 (by decide),
    hcast 6 8 (by decide), hcast 7 17 (by decide),
    hcast 8 16 (by decide), hcast 9 11 (by decide),
    hcast 10 9 (by decide), hcast 11 22 (by decide),
    hcast 12 18 (by decide), hcast 13 21 (by decide),
    hcast 14 13 (by decide), hcast 15 19 (by decide),
    hcast 16 3 (by decide), hcast 17 15 (by decide),
    hcast 18 6 (by decide), hcast 19 7 (by decide),
    hcast 20 12 (by decide), hcast 21 14 (by decide)]
  ring

/-- Every residue-weighted character sum is the evaluation of
`characterSumPolynomial` at the character's value on the primitive residue
`5`. -/
theorem weightedCharacterSum_eq_eval_characterSumPolynomial
    (chi : DirichletCharacter ℂ 23) :
    ∑ j : ZMod 23, chi j * (j.val : ℂ) =
      Polynomial.eval (chi 5)
        (characterSumPolynomial.map (algebraMap ℚ ℂ)) := by
  rw [weightedCharacterSum_eq_sum_fivePowers]
  exact sum_fivePowers_eq_eval_characterSumPolynomial chi

/-- Evaluation at the primitive residue `5` distinguishes all complex
Dirichlet characters modulo `23`. -/
theorem evaluationAtFive_injective :
    Function.Injective (fun chi : DirichletCharacter ℂ 23 ↦ chi 5) := by
  intro chi psi heval
  change chi 5 = psi 5 at heval
  ext a
  have ha : (a : ZMod 23) ≠ 0 := Units.ne_zero a
  have ha_image :
      (a : ZMod 23) ∈
        Finset.univ.image (fun k : Fin 22 ↦ (5 : ZMod 23) ^ (k : ℕ)) := by
    have ha_univ : (a : ZMod 23) ∈ (Finset.univ : Finset (ZMod 23)) :=
      Finset.mem_univ _
    rw [univ_zmodTwentyThree_eq_insert_zero_image_fivePowers] at ha_univ
    simpa only [Finset.mem_insert, ha, false_or] using ha_univ
  obtain ⟨k, _hk, hk⟩ := Finset.mem_image.mp ha_image
  rw [← hk, map_pow, map_pow, heval]

/-- The values at `5` of the eleven odd characters are exactly the roots of
the mapped polynomial `X^11 + 1`. -/
theorem prod_X_sub_C_oddCharactersTwentyThree_eval_five_eq_rootPolynomial :
    (∏ chi ∈ oddCharacters23,
        (Polynomial.X - Polynomial.C (chi (5 : ZMod 23)))) =
      oddCharacterRootPolynomial.map (algebraMap ℚ ℂ) := by
  classical
  have hdvd :
      (∏ chi ∈ oddCharacters23,
          (Polynomial.X - Polynomial.C (chi (5 : ZMod 23)))) ∣
        (Polynomial.X ^ 11 + 1 : Polynomial ℂ) := by
    apply Finset.prod_dvd_of_coprime
    · intro chi hchi psi hpsi hne
      exact Polynomial.pairwise_coprime_X_sub_C evaluationAtFive_injective hne
    · intro chi hchi
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, ← map_pow]
      rw [show (5 : ZMod 23) ^ 11 = -1 by decide]
      have hodd : chi.Odd := by
        simpa only [oddCharacters23, Finset.mem_filter, Finset.mem_univ,
          true_and] using hchi
      rw [hodd]
      norm_num
  have hp :
      (∏ chi ∈ oddCharacters23,
        (Polynomial.X - Polynomial.C (chi (5 : ZMod 23)))).Monic := by
    apply Polynomial.monic_prod_of_monic
    intro chi hchi
    exact Polynomial.monic_X_sub_C _
  have htarget : (Polynomial.X ^ 11 + (1 : Polynomial ℂ)).Monic := by
    simpa only [Polynomial.C_1] using
      (Polynomial.monic_X_pow_add_C (a := (1 : ℂ)) (by norm_num : 11 ≠ 0))
  have hdeg : (Polynomial.X ^ 11 + (1 : Polynomial ℂ)).natDegree ≤
      (∏ chi ∈ oddCharacters23,
        (Polynomial.X - Polynomial.C (chi (5 : ZMod 23)))).natDegree := by
    rw [show (1 : Polynomial ℂ) = Polynomial.C 1 by simp,
      Polynomial.natDegree_X_pow_add_C]
    simp only [Polynomial.natDegree_finsetProd_X_sub_C_eq_card,
      card_oddCharacters23]
    exact le_rfl
  have hprod :
      (∏ chi ∈ oddCharacters23,
          (Polynomial.X - Polynomial.C (chi (5 : ZMod 23)))) =
        Polynomial.X ^ 11 + 1 :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hp htarget hdvd hdeg).symm
  rw [hprod]
  simp [oddCharacterRootPolynomial]

/-- The resultant of the odd-character root product is the product of the
second polynomial evaluated at all eleven character values. -/
theorem resultant_prod_X_sub_C_oddCharactersTwentyThree_eval_five
    (q : Polynomial ℂ) :
    (∏ chi ∈ oddCharacters23,
        (Polynomial.X - Polynomial.C (chi (5 : ZMod 23)))).resultant q =
      ∏ chi ∈ oddCharacters23, Polynomial.eval (chi 5) q := by
  classical
  change
    (∏ chi ∈ oddCharacters23,
      (Polynomial.X - Polynomial.C (chi (5 : ZMod 23)))).resultant q
        (∏ chi ∈ oddCharacters23,
          (Polynomial.X - Polynomial.C (chi (5 : ZMod 23)))).natDegree
        q.natDegree = _
  rw [Polynomial.resultant_prod_left oddCharacters23
    (fun chi ↦ Polynomial.X - Polynomial.C (chi (5 : ZMod 23))) q
    q.natDegree (by simp) le_rfl]
  simp

/-- The product of the eleven evaluations is the rational resultant mapped
to `ℂ`. -/
theorem prod_eval_characterSumPolynomial_eq_mapped_resultant :
    (∏ chi ∈ oddCharacters23,
        Polynomial.eval (chi 5)
          (characterSumPolynomial.map (algebraMap ℚ ℂ))) =
      algebraMap ℚ ℂ
        (oddCharacterRootPolynomial.resultant characterSumPolynomial) := by
  rw [← resultant_prod_X_sub_C_oddCharactersTwentyThree_eval_five]
  rw [prod_X_sub_C_oddCharactersTwentyThree_eval_five_eq_rootPolynomial]
  simp

/-- Exact product of the eleven character-sum polynomial evaluations. -/
theorem prod_eval_characterSumPolynomial_eq_neg_three_mul_fortySix_pow_ten :
    (∏ chi ∈ oddCharacters23,
        Polynomial.eval (chi 5)
          (characterSumPolynomial.map (algebraMap ℚ ℂ))) =
      (-3 : ℂ) * 46 ^ 10 := by
  rw [prod_eval_characterSumPolynomial_eq_mapped_resultant,
    characterSumPolynomial_resultant]
  norm_num

/-- Exact product of the eleven residue-weighted odd-character sums. -/
theorem prod_weightedCharacterSum_eq_neg_three_mul_fortySix_pow_ten :
    (∏ chi ∈ oddCharacters23,
        (∑ j : ZMod 23, chi j * (j.val : ℂ))) =
      (-3 : ℂ) * 46 ^ 10 := by
  calc
    (∏ chi ∈ oddCharacters23,
        (∑ j : ZMod 23, chi j * (j.val : ℂ))) =
        ∏ chi ∈ oddCharacters23,
          Polynomial.eval (chi 5)
            (characterSumPolynomial.map (algebraMap ℚ ℂ)) := by
      apply Finset.prod_congr rfl
      intro chi hchi
      exact weightedCharacterSum_eq_eval_characterSumPolynomial chi
    _ = (-3 : ℂ) * 46 ^ 10 :=
      prod_eval_characterSumPolynomial_eq_neg_three_mul_fortySix_pow_ten

/-- The exact finite product of the analytically continued odd Dirichlet
`L`-values at zero modulo `23`. -/
theorem prod_oddCharactersTwentyThree_LFunction_zero_eq :
    (∏ chi ∈ oddCharacters23, DirichletCharacter.LFunction chi 0) =
      (3 : ℂ) * 2 ^ 10 / 23 := by
  have hL (chi : DirichletCharacter ℂ 23) (hchi : chi ∈ oddCharacters23) :
      DirichletCharacter.LFunction chi 0 =
        -(∑ j : ZMod 23, chi j * (j.val : ℂ)) / 23 := by
    apply DirichletCharacter.Odd.LFunction_apply_zero_weighted_sum
    simpa only [oddCharacters23, Finset.mem_filter, Finset.mem_univ,
      true_and] using hchi
  have hterm (chi : DirichletCharacter ℂ 23) :
      -(∑ j : ZMod 23, chi j * (j.val : ℂ)) / 23 =
        ((-1 : ℂ) / 23) * (∑ j : ZMod 23, chi j * (j.val : ℂ)) := by
    ring
  calc
    (∏ chi ∈ oddCharacters23, DirichletCharacter.LFunction chi 0) =
        ∏ chi ∈ oddCharacters23,
          (-(∑ j : ZMod 23, chi j * (j.val : ℂ)) / 23) := by
      apply Finset.prod_congr rfl
      intro chi hchi
      exact hL chi hchi
    _ = ∏ chi ∈ oddCharacters23,
          (((-1 : ℂ) / 23) * (∑ j : ZMod 23, chi j * (j.val : ℂ))) := by
      apply Finset.prod_congr rfl
      intro chi hchi
      exact hterm chi
    _ = (((-1 : ℂ) / 23) ^ oddCharacters23.card) *
          (∏ chi ∈ oddCharacters23,
            (∑ j : ZMod 23, chi j * (j.val : ℂ))) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const]
    _ = (3 : ℂ) * 2 ^ 10 / 23 := by
      rw [card_oddCharacters23,
        prod_weightedCharacterSum_eq_neg_three_mul_fortySix_pow_ten]
      norm_num [div_pow]

/-- The normalization used in the relative class-number formula makes the
finite odd-character `L(0)` product exactly `3`. -/
theorem normalized_prod_oddCharactersTwentyThree_LFunction_zero_eq_three :
    ((23 : ℂ) / 2 ^ 10) *
        (∏ chi ∈ oddCharacters23,
          DirichletCharacter.LFunction chi 0) = 3 := by
  rw [prod_oddCharactersTwentyThree_LFunction_zero_eq]
  norm_num

end

end BealRegular.TwentyThreeOddCharacterProduct
