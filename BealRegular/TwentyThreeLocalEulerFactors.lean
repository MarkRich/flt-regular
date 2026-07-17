import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Local Euler-factor identities at `23`

This module proves the finite polynomial identities behind the unramified
local factors of
`zeta_{Q(zeta_23)} / zeta_{Q(zeta_23)^+}` and the eleven odd Dirichlet
characters modulo `23`.

These identities are local and algebraic. They do **not** prove the global
Dedekind-zeta factorization. The ramified prime `23`, a Dedekind-zeta Euler
product, and the analytic or meromorphic continuation step remain separate.
-/

open scoped BigOperators
open scoped NumberField

noncomputable section

namespace BealRegular

open DirichletCharacter
open NumberField

local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

private theorem card_units_zmod23 : Nat.card ((ZMod 23)ˣ) = 22 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime (by decide : Nat.Prime 23)]

/-- Every unit modulo `23` has order `1`, `2`, `11`, or `22`. -/
theorem orderOf_unit_zmodTwentyThree_cases (u : (ZMod 23)ˣ) :
    orderOf u = 1 ∨ orderOf u = 2 ∨ orderOf u = 11 ∨ orderOf u = 22 := by
  have hdvd : orderOf u ∣ 22 := by
    rw [← card_units_zmod23]
    exact orderOf_dvd_natCard u
  have hle : orderOf u ≤ 22 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hcase : orderOf u <;> norm_num at hdvd <;> simp_all

/-- The finite set of odd Dirichlet characters modulo `23`. -/
def oddCharacters23 : Finset (DirichletCharacter ℂ 23) :=
  by
    classical
    exact Finset.univ.filter DirichletCharacter.Odd

@[simp]
theorem mem_oddCharacters23 (χ : DirichletCharacter ℂ 23) :
    χ ∈ oddCharacters23 ↔ χ.Odd := by
  classical
  simp [oddCharacters23]

private theorem two_mul_sum_oddCharacters23_apply (a : ZMod 23) :
    2 * ∑ χ ∈ oddCharacters23, χ a =
      (∑ χ : DirichletCharacter ℂ 23, χ a) -
        ∑ χ : DirichletCharacter ℂ 23, χ (-a) := by
  classical
  rw [Finset.mul_sum]
  calc
    ∑ χ ∈ oddCharacters23, 2 * χ a =
        ∑ χ ∈ oddCharacters23, (χ a - χ (-a)) := by
      apply Finset.sum_congr rfl
      intro χ hχ
      simp only [oddCharacters23, Finset.mem_filter] at hχ
      rw [hχ.2.eval_neg]
      ring
    _ = ∑ χ : DirichletCharacter ℂ 23, (χ a - χ (-a)) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro χ hχ hχodd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχodd
      rcases χ.even_or_odd with hχeven | hχodd'
      · rw [hχeven.eval_neg]
        ring
      · exact (hχodd hχodd').elim
    _ = (∑ χ : DirichletCharacter ℂ 23, χ a) -
          ∑ χ : DirichletCharacter ℂ 23, χ (-a) := by
      exact Finset.sum_sub_distrib
        (s := Finset.univ) (fun χ : DirichletCharacter ℂ 23 ↦ χ a) (fun χ ↦ χ (-a))

/-- Orthogonality for the odd characters modulo `23`. -/
theorem sum_oddCharacters23_apply (a : ZMod 23) :
    ∑ χ ∈ oddCharacters23, χ a =
      if a = 1 then 11 else if a = -1 then -11 else 0 := by
  classical
  have h := two_mul_sum_oddCharacters23_apply a
  rw [sum_characters_eq, sum_characters_eq] at h
  have hp : Nat.Prime 23 := by decide
  rw [Nat.totient_prime hp] at h
  norm_num at h
  have h' :
      2 * ∑ χ ∈ oddCharacters23, χ a =
        (if a = 1 then 22 else 0) - (if a = -1 then 22 else 0) := by
    simpa only [neg_eq_iff_eq_neg] using h
  by_cases ha1 : a = 1
  · subst a
    have hone : (1 : ZMod 23) ≠ -1 := by decide
    simp only [if_pos, hone, if_false] at h' ⊢
    linear_combination h' / 2
  by_cases han1 : a = -1
  · subst a
    have hminus : (-1 : ZMod 23) ≠ 1 := by decide
    simp only [hminus, if_false, if_pos] at h' ⊢
    linear_combination h' / 2
  · simp only [ha1, han1, if_false] at h' ⊢
    linear_combination h' / 2

/-- The same odd-character orthogonality identity after taking a power. -/
theorem sum_oddCharacters23_apply_pow (a : ZMod 23) (k : ℕ) :
    ∑ χ ∈ oddCharacters23, (χ a) ^ k =
      if a ^ k = 1 then 11 else if a ^ k = -1 then -11 else 0 := by
  simpa only [map_pow] using sum_oddCharacters23_apply (a ^ k)

private theorem zpowers_unit_eq_top_of_val_pow_eleven_eq_neg_one
    (u : (ZMod 23)ˣ) (hu : (u : ZMod 23) ^ 11 = -1)
    (huNeg : (u : ZMod 23) ≠ -1) :
    Subgroup.zpowers u = ⊤ := by
  have hu11 : u ^ 11 ≠ 1 := by
    intro h
    apply_fun ((↑·) : (ZMod 23)ˣ → ZMod 23) at h
    simp only [Units.val_pow_eq_pow_val, Units.val_one, hu] at h
    exact (by decide : (-1 : ZMod 23) ≠ 1) h
  have hu22 : u ^ 22 = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    rw [show 22 = 11 * 2 by norm_num, pow_mul, hu]
    norm_num
  have hdvd : orderOf u ∣ 22 := orderOf_dvd_of_pow_eq_one hu22
  have hnot : ¬ orderOf u ∣ 11 := by
    intro hdvd11
    exact hu11 (orderOf_dvd_iff_pow_eq_one.mp hdvd11)
  have horder : orderOf u = 22 := by
    have hne2 : orderOf u ≠ 2 := by
      intro hord
      apply huNeg
      have hu2 : u ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by simp [hord])
      have hu11eq : u ^ 11 = u := by
        rw [show 11 = 2 * 5 + 1 by norm_num, pow_add, pow_mul, hu2]
        simp
      apply_fun ((↑·) : (ZMod 23)ˣ → ZMod 23) at hu11eq
      simpa only [Units.val_pow_eq_pow_val, hu] using hu11eq.symm
    have hle : orderOf u ≤ 22 := Nat.le_of_dvd (by norm_num) hdvd
    have hcases : orderOf u = 1 ∨ orderOf u = 2 ∨ orderOf u = 11 ∨ orderOf u = 22 := by
      interval_cases hcase : orderOf u <;> norm_num at hdvd <;> simp_all
    rcases hcases with h1 | h2 | h11 | h22
    · exact (hnot (h1 ▸ by norm_num)).elim
    · exact (hne2 h2).elim
    · exact (hnot (h11 ▸ by norm_num)).elim
    · exact h22
  have hcard : Nat.card ((ZMod 23)ˣ) = 22 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (by decide : Nat.Prime 23)]
  apply (Subgroup.card_eq_iff_eq_top (Subgroup.zpowers u)).mp
  rw [Nat.card_zpowers, horder, hcard]

private theorem oddEvaluation_injective_of_pow_eleven_eq_neg_one
    (a : ZMod 23) (ha : a ^ 11 = -1) (haNeg : a ≠ -1) :
    Function.Injective (fun χ : DirichletCharacter ℂ 23 ↦ χ a) := by
  intro χ ψ hχψ
  have ha0 : a ≠ 0 := by
    intro ha0
    have hzero : (0 : ZMod 23) ≠ -1 := by decide
    apply hzero
    simpa only [ha0, zero_pow (by norm_num : 11 ≠ 0)] using ha
  let haUnit : IsUnit a := isUnit_iff_ne_zero.mpr ha0
  let u : (ZMod 23)ˣ := haUnit.unit
  have hu_spec : (u : ZMod 23) = a := haUnit.unit_spec
  have hu : (u : ZMod 23) ^ 11 = -1 := by simpa only [hu_spec] using ha
  have huNeg : (u : ZMod 23) ≠ -1 := by simpa only [hu_spec] using haNeg
  apply (DirichletCharacter.toUnitHom_inj χ ψ).mp
  ext v
  have hv : v ∈ Subgroup.zpowers u := by
    rw [zpowers_unit_eq_top_of_val_pow_eleven_eq_neg_one u hu huNeg]
    exact Subgroup.mem_top v
  obtain ⟨n, rfl⟩ := hv
  have hbase : χ.toUnitHom u = ψ.toUnitHom u := by
    apply Units.ext
    simpa only [MulChar.coe_toUnitHom, hu_spec] using hχψ
  simp only [map_zpow, hbase]

private theorem closure_pair_eq_top_of_order_eleven
    (u : (ZMod 23)ˣ) (hu : orderOf u = 11) :
    Subgroup.closure ({u, -1} : Set ((ZMod 23)ˣ)) = ⊤ := by
  let H : Subgroup ((ZMod 23)ˣ) := Subgroup.closure ({u, -1} : Set ((ZMod 23)ˣ))
  have huH : u ∈ H := Subgroup.subset_closure (by simp)
  have hnegH : (-1 : (ZMod 23)ˣ) ∈ H := Subgroup.subset_closure (by simp)
  have h11 : 11 ∣ Nat.card H := by
    rw [← hu, ← Subgroup.orderOf_mk u huH]
    exact orderOf_dvd_natCard (⟨u, huH⟩ : H)
  have hnegOrder : orderOf (-1 : (ZMod 23)ˣ) = 2 := by
    rw [← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one]
    norm_num [ringChar.eq (ZMod 23) 23]
  have h2 : 2 ∣ Nat.card H := by
    rw [← hnegOrder, ← Subgroup.orderOf_mk (-1 : (ZMod 23)ˣ) hnegH]
    exact orderOf_dvd_natCard (⟨-1, hnegH⟩ : H)
  have h22 : 22 ∣ Nat.card H := by
    exact (by norm_num : Nat.Coprime 2 11).mul_dvd_of_dvd_of_dvd h2 h11
  have hle : Nat.card H ≤ 22 := by
    rw [← card_units_zmod23]
    exact Nat.card_le_card_of_injective ((↑·) : H → (ZMod 23)ˣ) Subtype.val_injective
  have hcard : Nat.card H = 22 :=
    Nat.le_antisymm hle (Nat.le_of_dvd Nat.card_pos h22)
  apply (Subgroup.card_eq_iff_eq_top H).mp
  rw [card_units_zmod23]
  exact hcard

private theorem oddEvaluation_injective_of_order_eleven
    (u : (ZMod 23)ˣ) (hu : orderOf u = 11) :
    Set.InjOn (fun χ : DirichletCharacter ℂ 23 ↦ χ (u : ZMod 23))
      { χ | χ.Odd } := by
  intro χ hχ ψ hψ hval
  apply (DirichletCharacter.toUnitHom_inj χ ψ).mp
  apply MonoidHom.eq_of_eqOn_dense (closure_pair_eq_top_of_order_eleven u hu)
  intro v hv
  rcases hv with (rfl | rfl)
  · apply Units.ext
    simpa only [MulChar.coe_toUnitHom] using hval
  · apply Units.ext
    simp only [MulChar.coe_toUnitHom, Units.val_neg, Units.val_one]
    rw [hχ, hψ]

/-- There are exactly eleven odd Dirichlet characters modulo `23`. -/
theorem card_oddCharacters23 : oddCharacters23.card = 11 := by
  have h := sum_oddCharacters23_apply (1 : ZMod 23)
  have hone : (1 : ZMod 23) ≠ -1 := by decide
  simp only [map_one, Finset.sum_const, nsmul_eq_mul, mul_one, if_pos, hone, if_false] at h
  exact_mod_cast h

/-- The monic polynomial whose roots are the values at `a` of the odd
Dirichlet characters modulo `23`. -/
private def oddCharacterLocalRootPolynomial23 (a : ZMod 23) : Polynomial ℂ :=
  ∏ χ ∈ oddCharacters23, (Polynomial.X - Polynomial.C (χ a))

private theorem oddCharacterLocalRootPolynomial23_eq_X_pow_eleven_add_one
    (a : ZMod 23) (ha : a ^ 11 = -1) (haNeg : a ≠ -1) :
    oddCharacterLocalRootPolynomial23 a = Polynomial.X ^ 11 + 1 := by
  classical
  have hinj := oddEvaluation_injective_of_pow_eleven_eq_neg_one a ha haNeg
  have hdvd : oddCharacterLocalRootPolynomial23 a ∣ Polynomial.X ^ 11 + 1 := by
    apply Finset.prod_dvd_of_coprime
    · intro χ hχ ψ hψ hne
      exact Polynomial.pairwise_coprime_X_sub_C hinj hne
    · intro χ hχ
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, ← map_pow, ha]
      have hodd : χ.Odd := by
        simpa only [oddCharacters23, Finset.mem_filter, Finset.mem_univ, true_and] using hχ
      rw [hodd]
      norm_num
  have hp : (oddCharacterLocalRootPolynomial23 a).Monic := by
    apply Polynomial.monic_prod_of_monic
    intro χ hχ
    exact Polynomial.monic_X_sub_C _
  have htarget : (Polynomial.X ^ 11 + (1 : Polynomial ℂ)).Monic := by
    simpa only [Polynomial.C_1] using
      (Polynomial.monic_X_pow_add_C (a := (1 : ℂ)) (by norm_num : 11 ≠ 0))
  have hdeg : (Polynomial.X ^ 11 + (1 : Polynomial ℂ)).natDegree ≤
      (oddCharacterLocalRootPolynomial23 a).natDegree := by
    rw [show (1 : Polynomial ℂ) = Polynomial.C 1 by simp,
      Polynomial.natDegree_X_pow_add_C]
    simp only [oddCharacterLocalRootPolynomial23,
      Polynomial.natDegree_finsetProd_X_sub_C_eq_card, card_oddCharacters23]
    exact le_rfl
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hp htarget hdvd hdeg).symm

private theorem oddCharacterLocalRootPolynomial23_eq_X_pow_eleven_sub_one
    (u : (ZMod 23)ˣ) (hu : orderOf u = 11) :
    oddCharacterLocalRootPolynomial23 (u : ZMod 23) =
      Polynomial.X ^ 11 - 1 := by
  classical
  have hu11 : u ^ 11 = 1 := by
    rw [← hu]
    exact pow_orderOf_eq_one u
  have huval11 : (u : ZMod 23) ^ 11 = 1 := by
    apply_fun ((↑·) : (ZMod 23)ˣ → ZMod 23) at hu11
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hu11
  have hinj := oddEvaluation_injective_of_order_eleven u hu
  have hdvd : oddCharacterLocalRootPolynomial23 (u : ZMod 23) ∣
      Polynomial.X ^ 11 - 1 := by
    apply Finset.prod_dvd_of_coprime
    · intro χ hχ ψ hψ hne
      apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      exact (sub_ne_zero.mpr (fun heval ↦ hne <| hinj
          (show χ.Odd from by
            simpa [oddCharacters23] using hχ)
          (show ψ.Odd from by
            simpa [oddCharacters23] using hψ)
          heval)).isUnit
    · intro χ hχ
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, ← map_pow, huval11, map_one, sub_self]
  have hp : (oddCharacterLocalRootPolynomial23 (u : ZMod 23)).Monic := by
    apply Polynomial.monic_prod_of_monic
    intro χ hχ
    exact Polynomial.monic_X_sub_C _
  have htarget : (Polynomial.X ^ 11 - (1 : Polynomial ℂ)).Monic := by
    simpa only [Polynomial.C_1] using
      (Polynomial.monic_X_pow_sub_C (1 : ℂ) (by norm_num : 11 ≠ 0))
  have hdeg : (Polynomial.X ^ 11 - (1 : Polynomial ℂ)).natDegree ≤
      (oddCharacterLocalRootPolynomial23 (u : ZMod 23)).natDegree := by
    rw [show (1 : Polynomial ℂ) = Polynomial.C 1 by simp,
      Polynomial.natDegree_X_pow_sub_C]
    simp only [oddCharacterLocalRootPolynomial23,
      Polynomial.natDegree_finsetProd_X_sub_C_eq_card, card_oddCharacters23]
    exact le_rfl
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hp htarget hdvd hdeg).symm

/-- The product of the eleven odd-character Euler denominator polynomials
modulo `23`, evaluated at the residue class `a`. -/
def oddCharacterEulerPolynomialTwentyThree (a : ZMod 23) : Polynomial ℂ :=
  ∏ χ ∈ oddCharacters23,
    (1 - Polynomial.C (χ a) * Polynomial.X)

/-- At the identity residue class, all eleven odd-character local roots are
`1`. -/
theorem oddCharacterEulerPolynomialTwentyThree_one :
    oddCharacterEulerPolynomialTwentyThree 1 =
      (1 - Polynomial.X) ^ 11 := by
  classical
  simp [oddCharacterEulerPolynomialTwentyThree, card_oddCharacters23]

/-- Order-`1` form of the odd-character local Euler polynomial. -/
theorem oddCharacterEulerPolynomialTwentyThree_of_orderOne
    (u : (ZMod 23)ˣ) (hu : orderOf u = 1) :
    oddCharacterEulerPolynomialTwentyThree (u : ZMod 23) =
      (1 - Polynomial.X) ^ 11 := by
  rw [orderOf_eq_one_iff] at hu
  subst u
  simpa using oddCharacterEulerPolynomialTwentyThree_one

/-- At the residue class `-1`, oddness makes all eleven local roots equal to
`-1`. -/
theorem oddCharacterEulerPolynomialTwentyThree_negOne :
    oddCharacterEulerPolynomialTwentyThree (-1) =
      (1 + Polynomial.X) ^ 11 := by
  classical
  rw [oddCharacterEulerPolynomialTwentyThree]
  calc
    ∏ χ ∈ oddCharacters23, (1 - Polynomial.C (χ (-1)) * Polynomial.X) =
        ∏ _χ ∈ oddCharacters23, (1 + Polynomial.X) := by
      apply Finset.prod_congr rfl
      intro χ hχ
      have hodd : χ.Odd := by
        simpa only [oddCharacters23, Finset.mem_filter, Finset.mem_univ, true_and] using hχ
      rw [hodd]
      simp
    _ = (1 + Polynomial.X) ^ 11 := by
      simp [card_oddCharacters23]

/-- Order-`2` form of the odd-character local Euler polynomial. -/
theorem oddCharacterEulerPolynomialTwentyThree_of_orderTwo
    (u : (ZMod 23)ˣ) (hu : orderOf u = 2) :
    oddCharacterEulerPolynomialTwentyThree (u : ZMod 23) =
      (1 + Polynomial.X) ^ 11 := by
  have hvalOrder : orderOf (u : ZMod 23) = 2 := by
    rw [orderOf_units]
    exact hu
  have hval : (u : ZMod 23) = -1 :=
    (CharP.orderOf_eq_two_iff 23 (by norm_num)).mp hvalOrder
  rw [hval]
  exact oddCharacterEulerPolynomialTwentyThree_negOne

private theorem reverse_oddCharacterLocalRootPolynomial23 (a : ZMod 23) :
    (oddCharacterLocalRootPolynomial23 a).reverse =
      oddCharacterEulerPolynomialTwentyThree a := by
  classical
  simp only [oddCharacterLocalRootPolynomial23, oddCharacterEulerPolynomialTwentyThree]
  induction oddCharacters23 using Finset.induction with
  | empty => simp [Polynomial.reverse]
  | @insert χ s hχ ih =>
      rw [Finset.prod_insert hχ, Finset.prod_insert hχ,
        Polynomial.reverse_mul_of_domain, ih]
      congr 1
      rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.reverse_add_C]
      simp [Polynomial.reverse, sub_eq_add_neg]

private theorem reverse_X_pow_eleven_add_one :
    (Polynomial.X ^ 11 + (1 : Polynomial ℂ)).reverse =
      1 + Polynomial.X ^ 11 := by
  rw [← Polynomial.C_1, Polynomial.reverse_add_C]
  simp [Polynomial.reverse]

private theorem reverse_X_pow_eleven_sub_one :
    (Polynomial.X ^ 11 - (1 : Polynomial ℂ)).reverse =
      1 - Polynomial.X ^ 11 := by
  rw [show (1 : Polynomial ℂ) = Polynomial.C 1 by simp, sub_eq_add_neg,
    ← Polynomial.C_neg, Polynomial.reverse_add_C]
  simp [Polynomial.reverse, sub_eq_add_neg]

/-- At every residue class of order `11` modulo `23`, the product of the
eleven odd-character Euler denominators is exactly `1 - X^11`. -/
theorem oddCharacterEulerPolynomialTwentyThree_of_orderEleven
    (u : (ZMod 23)ˣ) (hu : orderOf u = 11) :
    oddCharacterEulerPolynomialTwentyThree (u : ZMod 23) =
      1 - Polynomial.X ^ 11 := by
  rw [← reverse_oddCharacterLocalRootPolynomial23 (u : ZMod 23),
    oddCharacterLocalRootPolynomial23_eq_X_pow_eleven_sub_one u hu,
    reverse_X_pow_eleven_sub_one]

private theorem oddCharacterLocalEulerPolynomial23_eq_one_add_X_pow_eleven
    (a : ZMod 23) (ha : a ^ 11 = -1) (haNeg : a ≠ -1) :
    oddCharacterEulerPolynomialTwentyThree a = 1 + Polynomial.X ^ 11 := by
  rw [← reverse_oddCharacterLocalRootPolynomial23 a,
    oddCharacterLocalRootPolynomial23_eq_X_pow_eleven_add_one a ha haNeg,
    reverse_X_pow_eleven_add_one]

private theorem val_pow_eleven_eq_negOne_of_orderTwentyTwo
    (u : (ZMod 23)ˣ) (hu : orderOf u = 22) :
    (u : ZMod 23) ^ 11 = -1 := by
  have hpowOrderUnit : orderOf (u ^ 11) = 2 := by
    calc
      orderOf (u ^ 11) = orderOf u / 11 :=
        orderOf_pow_of_dvd (by norm_num) (by rw [hu]; norm_num)
      _ = 2 := by norm_num [hu]
  have hpowOrder : orderOf ((u : ZMod 23) ^ 11) = 2 := by
    rw [← Units.val_pow_eq_pow_val, orderOf_units]
    exact hpowOrderUnit
  exact (CharP.orderOf_eq_two_iff 23 (by norm_num)).mp hpowOrder

private theorem val_ne_negOne_of_orderTwentyTwo
    (u : (ZMod 23)ˣ) (hu : orderOf u = 22) :
    (u : ZMod 23) ≠ -1 := by
  intro hneg
  have hvalOrder : orderOf (u : ZMod 23) = 2 :=
    (CharP.orderOf_eq_two_iff 23 (by norm_num)).mpr hneg
  rw [orderOf_units] at hvalOrder
  omega

/-- Order-`22` form of the odd-character local Euler polynomial. -/
theorem oddCharacterEulerPolynomialTwentyThree_of_orderTwentyTwo
    (u : (ZMod 23)ˣ) (hu : orderOf u = 22) :
    oddCharacterEulerPolynomialTwentyThree (u : ZMod 23) =
      1 + Polynomial.X ^ 11 :=
  oddCharacterLocalEulerPolynomial23_eq_one_add_X_pow_eleven (u : ZMod 23)
    (val_pow_eleven_eq_negOne_of_orderTwentyTwo u hu)
    (val_ne_negOne_of_orderTwentyTwo u hu)

/-- The order-`1` local denominator factorization for the cyclotomic field,
its real subfield, and the eleven odd characters. -/
theorem cyclotomicRealOdd_localEulerFactor_identity_orderOne
    (u : (ZMod 23)ˣ) (hu : orderOf u = 1) :
    (1 - Polynomial.X) ^ 22 =
      (1 - Polynomial.X) ^ 11 *
        oddCharacterEulerPolynomialTwentyThree (u : ZMod 23) := by
  rw [oddCharacterEulerPolynomialTwentyThree_of_orderOne u hu]
  ring

/-- The order-`2` local denominator factorization for the cyclotomic field,
its real subfield, and the eleven odd characters. -/
theorem cyclotomicRealOdd_localEulerFactor_identity_orderTwo
    (u : (ZMod 23)ˣ) (hu : orderOf u = 2) :
    (1 - Polynomial.X ^ 2) ^ 11 =
      (1 - Polynomial.X) ^ 11 *
        oddCharacterEulerPolynomialTwentyThree (u : ZMod 23) := by
  rw [oddCharacterEulerPolynomialTwentyThree_of_orderTwo u hu]
  ring

/-- The order-`11` local denominator factorization for the cyclotomic field,
its real subfield, and the eleven odd characters. -/
theorem cyclotomicRealOdd_localEulerFactor_identity_orderEleven
    (u : (ZMod 23)ˣ) (hu : orderOf u = 11) :
    (1 - Polynomial.X ^ 11) ^ 2 =
      (1 - Polynomial.X ^ 11) *
        oddCharacterEulerPolynomialTwentyThree (u : ZMod 23) := by
  rw [oddCharacterEulerPolynomialTwentyThree_of_orderEleven u hu]
  simp [pow_two]

/-- The order-`22` local denominator factorization for the cyclotomic field,
its real subfield, and the eleven odd characters. -/
theorem cyclotomicRealOdd_localEulerFactor_identity_orderTwentyTwo
    (u : (ZMod 23)ˣ) (hu : orderOf u = 22) :
    1 - Polynomial.X ^ 22 =
      (1 - Polynomial.X ^ 11) *
        oddCharacterEulerPolynomialTwentyThree (u : ZMod 23) := by
  rw [oddCharacterEulerPolynomialTwentyThree_of_orderTwentyTwo u hu]
  ring

/-- The four exhaustive possibilities for the odd-character Euler polynomial
at any nonzero residue class modulo `23`. -/
theorem oddCharacterEulerPolynomialTwentyThree_order_cases
    (u : (ZMod 23)ˣ) :
    (orderOf u = 1 ∧
      oddCharacterEulerPolynomialTwentyThree (u : ZMod 23) =
        (1 - Polynomial.X) ^ 11) ∨
    (orderOf u = 2 ∧
      oddCharacterEulerPolynomialTwentyThree (u : ZMod 23) =
        (1 + Polynomial.X) ^ 11) ∨
    (orderOf u = 11 ∧
      oddCharacterEulerPolynomialTwentyThree (u : ZMod 23) =
        1 - Polynomial.X ^ 11) ∨
    (orderOf u = 22 ∧
      oddCharacterEulerPolynomialTwentyThree (u : ZMod 23) =
        1 + Polynomial.X ^ 11) := by
  rcases orderOf_unit_zmodTwentyThree_cases u with h1 | h2 | h11 | h22
  · exact Or.inl ⟨h1, oddCharacterEulerPolynomialTwentyThree_of_orderOne u h1⟩
  · exact Or.inr <| Or.inl
      ⟨h2, oddCharacterEulerPolynomialTwentyThree_of_orderTwo u h2⟩
  · exact Or.inr <| Or.inr <| Or.inl
      ⟨h11, oddCharacterEulerPolynomialTwentyThree_of_orderEleven u h11⟩
  · exact Or.inr <| Or.inr <| Or.inr
      ⟨h22, oddCharacterEulerPolynomialTwentyThree_of_orderTwentyTwo u h22⟩

/-- A single exhaustive local factorization theorem for
`zeta_{Q(zeta_23)} / zeta_{Q(zeta_23)^+}` away from `23`. -/
theorem cyclotomicRealOdd_localEulerFactor_order_cases
    (u : (ZMod 23)ˣ) :
    (orderOf u = 1 ∧
      (1 - Polynomial.X) ^ 22 =
        (1 - Polynomial.X) ^ 11 *
          oddCharacterEulerPolynomialTwentyThree (u : ZMod 23)) ∨
    (orderOf u = 2 ∧
      (1 - Polynomial.X ^ 2) ^ 11 =
        (1 - Polynomial.X) ^ 11 *
          oddCharacterEulerPolynomialTwentyThree (u : ZMod 23)) ∨
    (orderOf u = 11 ∧
      (1 - Polynomial.X ^ 11) ^ 2 =
        (1 - Polynomial.X ^ 11) *
          oddCharacterEulerPolynomialTwentyThree (u : ZMod 23)) ∨
    (orderOf u = 22 ∧
      1 - Polynomial.X ^ 22 =
        (1 - Polynomial.X ^ 11) *
          oddCharacterEulerPolynomialTwentyThree (u : ZMod 23)) := by
  rcases orderOf_unit_zmodTwentyThree_cases u with h1 | h2 | h11 | h22
  · exact Or.inl ⟨h1, cyclotomicRealOdd_localEulerFactor_identity_orderOne u h1⟩
  · exact Or.inr <| Or.inl
      ⟨h2, cyclotomicRealOdd_localEulerFactor_identity_orderTwo u h2⟩
  · exact Or.inr <| Or.inr <| Or.inl
      ⟨h11, cyclotomicRealOdd_localEulerFactor_identity_orderEleven u h11⟩
  · exact Or.inr <| Or.inr <| Or.inr
      ⟨h22, cyclotomicRealOdd_localEulerFactor_identity_orderTwentyTwo u h22⟩

private theorem natCast_zmodTwentyThree_ne_zero_of_prime
    {q : ℕ} (hq : Nat.Prime q) (hq23 : q ≠ 23) :
    (q : ZMod 23) ≠ 0 := by
  intro hzero
  have h23dvdq : 23 ∣ q := (ZMod.natCast_eq_zero_iff q 23).mp hzero
  rcases (Nat.dvd_prime hq).mp h23dvdq with h23one | h23q
  · norm_num at h23one
  · exact hq23 h23q.symm

/-- For every rational prime `q ≠ 23`, the four odd-character local
polynomial cases apply directly to its residue class modulo `23`. -/
theorem oddCharacterEulerPolynomialTwentyThree_prime_order_cases
    {q : ℕ} (hq : Nat.Prime q) (hq23 : q ≠ 23) :
    (orderOf (q : ZMod 23) = 1 ∧
      oddCharacterEulerPolynomialTwentyThree (q : ZMod 23) =
        (1 - Polynomial.X) ^ 11) ∨
    (orderOf (q : ZMod 23) = 2 ∧
      oddCharacterEulerPolynomialTwentyThree (q : ZMod 23) =
        (1 + Polynomial.X) ^ 11) ∨
    (orderOf (q : ZMod 23) = 11 ∧
      oddCharacterEulerPolynomialTwentyThree (q : ZMod 23) =
        1 - Polynomial.X ^ 11) ∨
    (orderOf (q : ZMod 23) = 22 ∧
      oddCharacterEulerPolynomialTwentyThree (q : ZMod 23) =
        1 + Polynomial.X ^ 11) := by
  let hqUnit : IsUnit (q : ZMod 23) :=
    isUnit_iff_ne_zero.mpr (natCast_zmodTwentyThree_ne_zero_of_prime hq hq23)
  let u : (ZMod 23)ˣ := hqUnit.unit
  have hu_spec : (u : ZMod 23) = q := hqUnit.unit_spec
  have hcases := oddCharacterEulerPolynomialTwentyThree_order_cases u
  rw [← orderOf_units] at hcases
  simpa only [hu_spec] using hcases

/-- For every rational prime `q ≠ 23`, the exact local denominator
factorization is one of the four displayed order cases. -/
theorem cyclotomicRealOdd_localEulerFactor_prime_order_cases
    {q : ℕ} (hq : Nat.Prime q) (hq23 : q ≠ 23) :
    (orderOf (q : ZMod 23) = 1 ∧
      (1 - Polynomial.X) ^ 22 =
        (1 - Polynomial.X) ^ 11 *
          oddCharacterEulerPolynomialTwentyThree (q : ZMod 23)) ∨
    (orderOf (q : ZMod 23) = 2 ∧
      (1 - Polynomial.X ^ 2) ^ 11 =
        (1 - Polynomial.X) ^ 11 *
          oddCharacterEulerPolynomialTwentyThree (q : ZMod 23)) ∨
    (orderOf (q : ZMod 23) = 11 ∧
      (1 - Polynomial.X ^ 11) ^ 2 =
        (1 - Polynomial.X ^ 11) *
          oddCharacterEulerPolynomialTwentyThree (q : ZMod 23)) ∨
    (orderOf (q : ZMod 23) = 22 ∧
      1 - Polynomial.X ^ 22 =
        (1 - Polynomial.X ^ 11) *
          oddCharacterEulerPolynomialTwentyThree (q : ZMod 23)) := by
  let hqUnit : IsUnit (q : ZMod 23) :=
    isUnit_iff_ne_zero.mpr (natCast_zmodTwentyThree_ne_zero_of_prime hq hq23)
  let u : (ZMod 23)ˣ := hqUnit.unit
  have hu_spec : (u : ZMod 23) = q := hqUnit.unit_spec
  have hcases := cyclotomicRealOdd_localEulerFactor_order_cases u
  rw [← orderOf_units] at hcases
  simpa only [hu_spec] using hcases

local notation "K23" => CyclotomicField 23 ℚ

local instance : IsCyclotomicExtension {23} ℚ K23 :=
  CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero 23 ℚ
local instance : IsGalois ℚ K23 :=
  IsCyclotomicExtension.isGalois {23} ℚ K23

/-- For every rational prime away from `23`, the number of primes above it in
`Q(zeta_23)`, multiplied by its residue degree, is exactly `22`. -/
theorem cyclotomic23_ncard_primesOver_mul_orderOf
    {q : ℕ} (hq : Nat.Prime q) (hq23 : q ≠ 23) :
    (Ideal.primesOver (Ideal.span {(q : ℤ)})
      (NumberField.RingOfIntegers K23)).ncard *
        orderOf (q : ZMod 23) = 22 := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hnot : ¬ q ∣ 23 := by
    intro hdvd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 23)).mp hdvd with hq1 | hqeq
    · exact hq.ne_one hq1
    · exact hq23 hqeq
  have hfund :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (Ideal.span {(q : ℤ)}) (NumberField.RingOfIntegers K23) Gal(K23/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd q K23 hnot,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd q K23 hnot,
    one_mul, IsGalois.card_aut_eq_finrank ℚ K23,
    IsCyclotomicExtension.Rat.finrank 23 K23,
    Nat.totient_prime (by decide : Nat.Prime 23)] at hfund
  norm_num at hfund ⊢
  exact hfund

end BealRegular
