import BealRegular.TwentyThreeAnalyticClassNumber
import BealRegular.TwentyThreeOddCharacterProduct
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# The odd-character analytic bridge at 23

This file reduces the remaining analytic input at exponent `23` to one
explicit proposition, `GlobalFactorizationTwentyThree`.  That proposition is
the factorization of the cyclotomic Dedekind zeta function by the maximal-real
subfield zeta function and the eleven odd Dirichlet `L`-series on
`Re(s) > 1`.

From that hypothesis the file takes the residue limit at `s = 1`, proves the
odd-character functional equations at `0` and `1`, determines the total root
number to be `+1` by positivity, and establishes the existing
`OddCharacterAnalyticBridgeTwentyThree`.  The already-proved finite product at
zero then gives class number `3`, regularity of `23`, and FLT at exponent `23`.
-/

open Filter NumberField Topology
open scoped BigOperators LSeries.notation NumberField

namespace BealRegular.TwentyThreeOddCharacterAnalyticBridge

open DirichletCharacter
open BealRegular.TwentyThreeAnalyticClassNumber
open BealRegular.TwentyThreeOddCharacterProduct
open BealRegular.TwentyThreeRelativeClassNumberResultant

noncomputable section

local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

local notation "K23" => CyclotomicField 23 ℚ
local notation "K23plus" => NumberField.maximalRealSubfield K23

/-- The sole global analytic input used by this file: the odd-character
factorization on the half-plane of absolute convergence. -/
def GlobalFactorizationTwentyThree : Prop :=
  ∀ s : ℂ, 1 < s.re →
    dedekindZeta K23 s =
      dedekindZeta K23plus s *
        ∏ χ ∈ BealRegular.oddCharacters23, L ↗χ s

/-- Every odd character modulo the prime `23` is primitive. -/
theorem oddCharacter_isPrimitive
    (χ : DirichletCharacter ℂ 23) (hχ : χ.Odd) :
    χ.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime (by decide : Nat.Prime 23)).mp χ.conductor_dvd_level with h | h
  · have hχ_one : χ = 1 :=
      (DirichletCharacter.eq_one_iff_conductor_eq_one).2 h
    exfalso
    apply hχ.not_even
    rw [hχ_one, DirichletCharacter.Even]
    exact MulChar.one_apply (isUnit_one.neg)
  · exact h

/-- The inverse of an odd character is odd. -/
theorem inv_odd
    (χ : DirichletCharacter ℂ 23) (hχ : χ.Odd) :
    χ⁻¹.Odd := by
  rw [DirichletCharacter.Odd, MulChar.inv_apply']
  change χ (-1) = -1 at hχ
  simpa only [inv_neg, inv_one] using hχ

/-- The Gauss sums of an odd character and its inverse multiply to `-23`. -/
theorem gaussSum_mul_gaussSum_inv_eq_neg_twentyThree
    (χ : DirichletCharacter ℂ 23) (hχ : χ.Odd) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar = -(23 : ℂ) := by
  have hχ_ne : χ ≠ 1 := by
    intro h
    apply hχ.not_even
    rw [h, DirichletCharacter.Even]
    exact MulChar.one_apply (isUnit_one.neg)
  have hprod := gaussSum_mul_gaussSum_eq_card
    (R := ZMod 23) (R' := ℂ) (χ := χ) hχ_ne (ZMod.isPrimitive_stdAddChar 23)
  have hshift := mul_gaussSum_inv_eq_gaussSum χ⁻¹
    (ZMod.stdAddChar : AddChar (ZMod 23) ℂ)
  have hneg : χ⁻¹ (-1) = (-1 : ℂ) := inv_odd χ hχ
  rw [hneg] at hshift
  norm_num at hprod
  calc
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar =
        gaussSum χ ZMod.stdAddChar *
          ((-1 : ℂ) * gaussSum χ⁻¹
            (ZMod.stdAddChar : AddChar (ZMod 23) ℂ)⁻¹) := by rw [hshift]
    _ = -(gaussSum χ ZMod.stdAddChar *
          gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod 23) ℂ)⁻¹) := by ring
    _ = -(23 : ℂ) := by rw [hprod]

/-- The square of the chosen complex square root of `23` is `23`. -/
theorem twentyThree_cpow_half_sq :
    (23 : ℂ) ^ (1 / 2 : ℂ) * (23 : ℂ) ^ (1 / 2 : ℂ) = 23 := by
  rw [← Complex.cpow_add (1 / 2 : ℂ) (1 / 2 : ℂ) (by norm_num : (23 : ℂ) ≠ 0)]
  norm_num

/-- Paired odd root numbers multiply to one. -/
theorem rootNumber_mul_inv_eq_one
    (χ : DirichletCharacter ℂ 23) (hχ : χ.Odd) :
    χ.rootNumber * χ⁻¹.rootNumber = 1 := by
  have hinv := inv_odd χ hχ
  rw [DirichletCharacter.rootNumber, DirichletCharacter.rootNumber]
  simp only [if_neg hχ.not_even, if_neg hinv.not_even, pow_one]
  have hg := gaussSum_mul_gaussSum_inv_eq_neg_twentyThree χ hχ
  have hs := twentyThree_cpow_half_sq
  calc
    gaussSum χ ZMod.stdAddChar / Complex.I / (23 : ℂ) ^ (1 / 2 : ℂ) *
          (gaussSum χ⁻¹ ZMod.stdAddChar / Complex.I / (23 : ℂ) ^ (1 / 2 : ℂ)) =
        (gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar) /
          ((Complex.I * Complex.I) *
            ((23 : ℂ) ^ (1 / 2 : ℂ) * (23 : ℂ) ^ (1 / 2 : ℂ))) := by ring
    _ = 1 := by rw [hg, hs]; norm_num

/-- Oddness is invariant under character inversion. -/
theorem odd_iff_inv_odd (χ : DirichletCharacter ℂ 23) :
    χ.Odd ↔ χ⁻¹.Odd := by
  constructor
  · exact inv_odd χ
  · intro h
    simpa using inv_odd χ⁻¹ h

/-- Inversion permutes the product of the eleven root numbers. -/
theorem prod_inv_rootNumber_eq_prod_rootNumber :
    (∏ χ ∈ BealRegular.oddCharacters23, χ⁻¹.rootNumber) =
      ∏ χ ∈ BealRegular.oddCharacters23, χ.rootNumber := by
  apply Finset.prod_equiv (Equiv.inv (DirichletCharacter ℂ 23))
  · intro χ
    simp only [BealRegular.mem_oddCharacters23]
    exact odd_iff_inv_odd χ
  · intro χ hχ
    rfl

/-- The total root number over all eleven odd characters has square one. -/
theorem prod_odd_rootNumber_sq_eq_one :
    (∏ χ ∈ BealRegular.oddCharacters23, χ.rootNumber) ^ 2 = 1 := by
  rw [pow_two]
  nth_rewrite 2 [← prod_inv_rootNumber_eq_prod_rootNumber]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro χ hχ
  exact rootNumber_mul_inv_eq_one χ
    ((BealRegular.mem_oddCharacters23 χ).mp hχ)

/-- The real gamma factor at `2`. -/
theorem GammaReal_two : Complex.Gammaℝ (2 : ℂ) = 1 / (Real.pi : ℂ) := by
  rw [Complex.Gammaℝ_def]
  norm_num [Complex.cpow_neg_one, Complex.Gamma_one]

/-- The individual odd-character functional equation between `L(χ,0)` and
`L(χ⁻¹,1)`. -/
theorem odd_LFunction_zero_eq_rootNumber_mul_LFunction_inv_one
    (χ : DirichletCharacter ℂ 23) (hχ : χ.Odd) :
    DirichletCharacter.LFunction χ 0 =
      (23 : ℂ) ^ (1 / 2 : ℂ) * χ.rootNumber *
        (DirichletCharacter.LFunction χ⁻¹ 1 / (Real.pi : ℂ)) := by
  simp only [DirichletCharacter.LFunction]
  have hinv := inv_odd χ hχ
  have hzero := ZMod.LFunction_eq_completed_div_gammaFactor_odd hχ.to_fun (0 : ℂ)
  simp only [zero_add, Complex.Gammaℝ_one, div_one] at hzero
  have hone := ZMod.LFunction_eq_completed_div_gammaFactor_odd hinv.to_fun (1 : ℂ)
  simp only [one_add_one_eq_two, GammaReal_two] at hone
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcompleted_one :
      DirichletCharacter.completedLFunction χ⁻¹ 1 =
        DirichletCharacter.LFunction χ⁻¹ 1 / (Real.pi : ℂ) := by
    simp only [DirichletCharacter.completedLFunction, DirichletCharacter.LFunction]
    rw [hone]
    field_simp
  have hfe := (oddCharacter_isPrimitive χ hχ).completedLFunction_one_sub (1 : ℂ)
  norm_num at hfe
  simp only [DirichletCharacter.completedLFunction] at hfe
  rw [← hzero] at hfe
  have hcompleted_one' := hcompleted_one
  simp only [DirichletCharacter.completedLFunction, DirichletCharacter.LFunction] at hcompleted_one'
  rw [hcompleted_one'] at hfe
  exact hfe

/-- Inversion also permutes the finite product of `L`-values at one. -/
theorem prod_inv_LFunction_one_eq_prod_LFunction_one :
    (∏ χ ∈ BealRegular.oddCharacters23,
        DirichletCharacter.LFunction χ⁻¹ 1) =
      ∏ χ ∈ BealRegular.oddCharacters23,
        DirichletCharacter.LFunction χ 1 := by
  apply Finset.prod_equiv (Equiv.inv (DirichletCharacter ℂ 23))
  · intro χ
    simp only [BealRegular.mem_oddCharacters23]
    exact odd_iff_inv_odd χ
  · intro χ hχ
    rfl

/-- The finite product of all eleven odd-character functional equations. -/
theorem prod_odd_LFunction_zero_functional_equation :
    (∏ χ ∈ BealRegular.oddCharacters23,
        DirichletCharacter.LFunction χ 0) =
      ((23 : ℂ) ^ (1 / 2 : ℂ)) ^ 11 *
        (∏ χ ∈ BealRegular.oddCharacters23, χ.rootNumber) *
          ((∏ χ ∈ BealRegular.oddCharacters23,
              DirichletCharacter.LFunction χ 1) / (Real.pi : ℂ) ^ 11) := by
  calc
    (∏ χ ∈ BealRegular.oddCharacters23,
        DirichletCharacter.LFunction χ 0) =
      ∏ χ ∈ BealRegular.oddCharacters23,
        ((23 : ℂ) ^ (1 / 2 : ℂ) * χ.rootNumber *
          (DirichletCharacter.LFunction χ⁻¹ 1 / (Real.pi : ℂ))) := by
            apply Finset.prod_congr rfl
            intro χ hχ
            exact odd_LFunction_zero_eq_rootNumber_mul_LFunction_inv_one χ
              ((BealRegular.mem_oddCharacters23 χ).mp hχ)
    _ = (∏ χ ∈ BealRegular.oddCharacters23, (23 : ℂ) ^ (1 / 2 : ℂ)) *
          (∏ χ ∈ BealRegular.oddCharacters23, χ.rootNumber) *
            (∏ χ ∈ BealRegular.oddCharacters23,
              (DirichletCharacter.LFunction χ⁻¹ 1 / (Real.pi : ℂ))) := by
          simp only [Finset.prod_mul_distrib]
    _ = ((23 : ℂ) ^ (1 / 2 : ℂ)) ^ 11 *
          (∏ χ ∈ BealRegular.oddCharacters23, χ.rootNumber) *
            ((∏ χ ∈ BealRegular.oddCharacters23,
                DirichletCharacter.LFunction χ 1) / (Real.pi : ℂ) ^ 11) := by
          rw [Finset.prod_const, BealRegular.card_oddCharacters23,
            Finset.prod_div_distrib, prod_inv_LFunction_one_eq_prod_LFunction_one,
            Finset.prod_const, BealRegular.card_oddCharacters23]

/-- No odd character modulo `23` is trivial. -/
theorem oddCharacter_ne_one {χ : DirichletCharacter ℂ 23}
    (hχ : χ ∈ BealRegular.oddCharacters23) : χ ≠ 1 := by
  have hodd : χ.Odd := (BealRegular.mem_oddCharacters23 χ).mp hχ
  intro hχone
  apply hodd.not_even
  rw [hχone, DirichletCharacter.Even]
  exact MulChar.one_apply (isUnit_one.neg)

/-- The finite product of odd `L`-functions tends to its value at one from
the right. -/
theorem tendsto_prod_odd_LFunction_one :
    Tendsto
      (fun t : ℝ ↦ ∏ χ ∈ BealRegular.oddCharacters23,
        DirichletCharacter.LFunction χ (t : ℂ))
      (𝓝[>] 1)
      (𝓝 (∏ χ ∈ BealRegular.oddCharacters23,
        DirichletCharacter.LFunction χ 1)) := by
  have hcast :
      Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).mono_left inf_le_left
  apply tendsto_finsetProd BealRegular.oddCharacters23
  intro χ hχ
  exact
    ((DirichletCharacter.differentiable_LFunction
      (oddCharacter_ne_one hχ)).continuous.continuousAt.tendsto.comp hcast)

/-- Taking the simple-pole boundary limit of
`GlobalFactorizationTwentyThree`. -/
theorem dedekindZeta_residue_ratio_eq_prod_odd_LFunction_one
    (hFactor : GlobalFactorizationTwentyThree) :
    (dedekindZeta_residue K23 : ℂ) /
        (dedekindZeta_residue K23plus : ℂ) =
      ∏ χ ∈ BealRegular.oddCharacters23,
        DirichletCharacter.LFunction χ 1 := by
  let P : ℝ → ℂ := fun t ↦
    ∏ χ ∈ BealRegular.oddCharacters23, DirichletCharacter.LFunction χ (t : ℂ)
  let P1 : ℂ :=
    ∏ χ ∈ BealRegular.oddCharacters23, DirichletCharacter.LFunction χ 1
  have hP : Tendsto P (𝓝[>] 1) (𝓝 P1) := by
    simpa [P, P1] using tendsto_prod_odd_LFunction_one
  have hK := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K23
  have hPlus :=
    NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K23plus
  have heq :
      (fun t : ℝ ↦ ((t : ℂ) - 1) * dedekindZeta K23 (t : ℂ)) =ᶠ[𝓝[>] 1]
        (fun t : ℝ ↦
          (((t : ℂ) - 1) * dedekindZeta K23plus (t : ℂ)) * P t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 1 < t at ht
    have htC : 1 < (t : ℂ).re := by simpa using ht
    have hprod :
        (∏ χ ∈ BealRegular.oddCharacters23, L ↗χ (t : ℂ)) = P t := by
      apply Finset.prod_congr rfl
      intro χ hχ
      exact (DirichletCharacter.LFunction_eq_LSeries χ htC).symm
    rw [hFactor (t : ℂ) htC, hprod]
    ring
  have hToResidueK :
      Tendsto
        (fun t : ℝ ↦
          (((t : ℂ) - 1) * dedekindZeta K23plus (t : ℂ)) * P t)
        (𝓝[>] 1) (𝓝 (dedekindZeta_residue K23 : ℂ)) :=
    hK.congr' heq
  have hToProduct :
      Tendsto
        (fun t : ℝ ↦
          (((t : ℂ) - 1) * dedekindZeta K23plus (t : ℂ)) * P t)
        (𝓝[>] 1)
        (𝓝 ((dedekindZeta_residue K23plus : ℂ) * P1)) :=
    hPlus.mul hP
  have hresidue :
      (dedekindZeta_residue K23 : ℂ) =
        (dedekindZeta_residue K23plus : ℂ) * P1 :=
    tendsto_nhds_unique hToResidueK hToProduct
  have hplus : (dedekindZeta_residue K23plus : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (NumberField.dedekindZeta_residue_ne_zero K23plus)
  apply (div_eq_iff hplus).2
  simpa [P1, mul_comm] using hresidue

/-- The complex half-power of `23` is its positive real square root. -/
theorem twentyThree_cpow_half_eq_sqrt :
    (23 : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 23 : ℂ) := by
  calc
    (23 : ℂ) ^ (1 / 2 : ℂ) =
        (((23 : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      symm
      simpa using
        (Complex.ofReal_cpow (show (0 : ℝ) ≤ 23 by positivity) (1 / 2 : ℝ))
    _ = (Real.sqrt 23 : ℂ) := by rw [Real.sqrt_eq_rpow]

/-- Positivity of the residue ratio determines the total root number as
`+1`, excluding the other square root of one. -/
theorem prod_odd_rootNumber_eq_one
    (hFactor : GlobalFactorizationTwentyThree) :
    (∏ χ ∈ BealRegular.oddCharacters23, χ.rootNumber) = 1 := by
  have hratio :=
    dedekindZeta_residue_ratio_eq_prod_odd_LFunction_one hFactor
  have hFE := prod_odd_LFunction_zero_functional_equation
  have hzero := prod_oddCharactersTwentyThree_LFunction_zero_eq
  have hsquare := prod_odd_rootNumber_sq_eq_one
  rcases (sq_eq_one_iff.mp hsquare) with hroot | hroot
  · exact hroot
  · exfalso
    rw [hzero, hroot, ← hratio, twentyThree_cpow_half_eq_sqrt] at hFE
    norm_cast at hFE
    have hFEreal :
        (3 * 2 ^ 10 : ℝ) / 23 =
          Real.sqrt 23 ^ 11 * (-1 : ℝ) *
            (NumberField.dedekindZeta_residue K23 /
              NumberField.dedekindZeta_residue K23plus / Real.pi ^ 11) := by
      apply Complex.ofReal_injective
      convert hFE using 1 <;>
        norm_num [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
    have hKpos : 0 < NumberField.dedekindZeta_residue K23 :=
      NumberField.dedekindZeta_residue_pos K23
    have hPpos : 0 < NumberField.dedekindZeta_residue K23plus :=
      NumberField.dedekindZeta_residue_pos K23plus
    have hsqrtpos : 0 < Real.sqrt 23 := Real.sqrt_pos.2 (by norm_num)
    have hpipos : 0 < Real.pi := Real.pi_pos
    have hleftpos : 0 < (3 * 2 ^ 10 : ℝ) / 23 := by positivity
    have hratioPos :
        0 < NumberField.dedekindZeta_residue K23 /
          NumberField.dedekindZeta_residue K23plus :=
      div_pos hKpos hPpos
    have hquotPos :
        0 < NumberField.dedekindZeta_residue K23 /
            NumberField.dedekindZeta_residue K23plus / Real.pi ^ 11 :=
      div_pos hratioPos (pow_pos hpipos 11)
    have hrightneg :
        Real.sqrt 23 ^ 11 * (-1 : ℝ) *
            (NumberField.dedekindZeta_residue K23 /
              NumberField.dedekindZeta_residue K23plus / Real.pi ^ 11) < 0 := by
      rw [show Real.sqrt 23 ^ 11 * (-1 : ℝ) *
          (NumberField.dedekindZeta_residue K23 /
            NumberField.dedekindZeta_residue K23plus / Real.pi ^ 11) =
        -(Real.sqrt 23 ^ 11 *
          (NumberField.dedekindZeta_residue K23 /
            NumberField.dedekindZeta_residue K23plus / Real.pi ^ 11)) by ring]
      exact neg_lt_zero.mpr (mul_pos (pow_pos hsqrtpos 11) hquotPos)
    linarith

/-- The global factorization supplies the exact analytic bridge already used
by the class-number module. -/
theorem oddCharacterAnalyticBridgeTwentyThree_of_globalFactorization
    (hFactor : GlobalFactorizationTwentyThree) :
    OddCharacterAnalyticBridgeTwentyThree := by
  have hratio :=
    dedekindZeta_residue_ratio_eq_prod_odd_LFunction_one hFactor
  have hFE := prod_odd_LFunction_zero_functional_equation
  have hzero := prod_oddCharactersTwentyThree_LFunction_zero_eq
  have hroot := prod_odd_rootNumber_eq_one hFactor
  rw [hzero, hroot, ← hratio, twentyThree_cpow_half_eq_sqrt] at hFE
  norm_cast at hFE
  have hFEreal :
      (3 * 2 ^ 10 : ℝ) / 23 =
        Real.sqrt 23 ^ 11 *
          (NumberField.dedekindZeta_residue K23 /
            NumberField.dedekindZeta_residue K23plus / Real.pi ^ 11) := by
    apply Complex.ofReal_injective
    convert hFE using 1 <;>
      norm_num [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
  have hsqrtSq : Real.sqrt 23 ^ 2 = (23 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  have hsqrtPow : Real.sqrt 23 ^ 11 = (23 : ℝ) ^ 5 * Real.sqrt 23 := by
    calc
      Real.sqrt 23 ^ 11 = (Real.sqrt 23 ^ 2) ^ 5 * Real.sqrt 23 := by ring
      _ = (23 : ℝ) ^ 5 * Real.sqrt 23 := by rw [hsqrtSq]
  rw [hsqrtPow] at hFEreal
  unfold OddCharacterAnalyticBridgeTwentyThree
  have hresultant :
      ((-(oddCharacterRootPolynomial.resultant characterSumPolynomial) /
          (46 : ℚ) ^ 10 : ℚ) : ℝ) = 3 := by
    norm_cast
    exact normalizedCharacterSumProduct
  rw [hresultant]
  have hP : NumberField.dedekindZeta_residue K23plus ≠ 0 :=
    NumberField.dedekindZeta_residue_ne_zero K23plus
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hP, hpi] at hFEreal ⊢
  nlinarith [hFEreal]

/-- The global factorization computes the cyclotomic class number as `3`. -/
theorem classNumber_eq_three_of_globalFactorization
    (hFactor : GlobalFactorizationTwentyThree) :
    NumberField.classNumber K23 = 3 :=
  classNumber_eq_three_of_oddCharacterAnalyticBridge
    (oddCharacterAnalyticBridgeTwentyThree_of_globalFactorization hFactor)

/-- The global factorization proves that `23` is a regular prime. -/
theorem isRegularPrime_twentyThree_of_globalFactorization
    (hFactor : GlobalFactorizationTwentyThree) :
    IsRegularPrime 23 :=
  isRegularPrime_twentyThree_of_oddCharacterAnalyticBridge
    (oddCharacterAnalyticBridgeTwentyThree_of_globalFactorization hFactor)

/-- The global factorization proves FLT for exponent `23`. -/
theorem fermatLastTheoremTwentyThree_of_globalFactorization
    (hFactor : GlobalFactorizationTwentyThree) :
    FermatLastTheoremFor 23 :=
  fermatLastTheoremTwentyThree_of_oddCharacterAnalyticBridge
    (oddCharacterAnalyticBridgeTwentyThree_of_globalFactorization hFactor)

end

end BealRegular.TwentyThreeOddCharacterAnalyticBridge
