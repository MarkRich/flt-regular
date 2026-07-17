module

public import BealRegular.TwentyThreeRealSubfieldPID
public import BealRegular.TwentyThreeHasseUnitIndex
public import BealRegular.TwentyThreeRelativeClassNumberResultant
public import FltRegular.FltRegular
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

/-!
# The analytic class-number constants at 23

This file specializes the analytic class-number formula to `ℚ(ζ₂₃)` and its
maximal real subfield.  All archimedean-place, torsion, discriminant, class
number, and CM-regulator constants are discharged, leaving the exact identity

`scaled Dedekind-zeta residue ratio = classNumber / indexRealUnits`.

The Hasse unit index is one by `TwentyThreeHasseUnitIndex`.  The remaining
Dirichlet-character argument is stated explicitly as
`OddCharacterAnalyticBridgeTwentyThree`: it identifies the scaled residue ratio
with the normalized odd-character resultant already kernel-computed in
`TwentyThreeRelativeClassNumberResultant`.  Every class-number, regularity, and
FLT consequence below retains that bridge as an explicit hypothesis.
-/

@[expose] public section

open NumberField NumberField.InfinitePlace NumberField.Units
open scoped NumberField

namespace BealRegular.TwentyThreeAnalyticClassNumber

open BealRegular.TwentyThreeRealSubfield
open BealRegular.TwentyThreeRealSubfieldRingOfIntegers
open BealRegular.TwentyThreeRealSubfieldPID
open BealRegular.TwentyThreeHasseUnitIndex
open BealRegular.TwentyThreeRelativeClassNumberResultant

noncomputable section

local notation "K23" => CyclotomicField 23 ℚ
local notation "K23plus" => NumberField.maximalRealSubfield K23

local instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩
local instance : IsCyclotomicExtension {23} ℚ K23 :=
  CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero 23 ℚ
local instance : NumberField.IsCMField K23 :=
  cyclotomicFieldTwentyThree_isCMField

private theorem cyclotomic_nrRealPlaces : nrRealPlaces K23 = 0 := by
  exact IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero K23 (by norm_num : 2 < 23)

private theorem cyclotomic_nrComplexPlaces : nrComplexPlaces K23 = 11 := by
  rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 23 K23,
    Nat.totient_prime (by norm_num : Nat.Prime 23)]

private theorem realSubfield_nrComplexPlaces : nrComplexPlaces K23plus = 0 := by
  exact NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K23plus

private theorem realSubfield_nrRealPlaces : nrRealPlaces K23plus = 11 := by
  have h := card_add_two_mul_card_eq_rank K23plus
  rw [realSubfield_nrComplexPlaces, maximalRealSubfield_finrank] at h
  omega

private theorem cyclotomic_unitRank : NumberField.Units.rank K23 = 10 := by
  simp [NumberField.Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces,
    cyclotomic_nrComplexPlaces]

private theorem cyclotomic_torsionOrder : torsionOrder K23 = 46 := by
  rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 23)]
  rw [if_neg (Nat.not_even_iff_odd.mpr ⟨11, by norm_num⟩)]

private theorem realSubfield_torsionOrder : torsionOrder K23plus = 2 := by
  apply torsionOrder_eq_two_of_odd_finrank
  rw [maximalRealSubfield_finrank]
  exact ⟨5, by norm_num⟩

private theorem cyclotomic_discr : NumberField.discr K23 = -(23 : ℤ) ^ 21 := by
  rw [IsCyclotomicExtension.Rat.discr_prime 23 K23]
  norm_num

private theorem sqrt_abs_cyclotomic_discr :
    Real.sqrt |(NumberField.discr K23 : ℝ)| = (23 : ℝ) ^ 10 * Real.sqrt 23 := by
  rw [cyclotomic_discr]
  simp only [Int.cast_neg, Int.cast_pow, Int.cast_ofNat]
  change Real.sqrt |(-(23 : ℝ) ^ 21)| = (23 : ℝ) ^ 10 * Real.sqrt 23
  rw [abs_neg, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 23)]
  have hp : (23 : ℝ) ^ 21 = ((23 : ℝ) ^ 10) ^ 2 * 23 := by ring
  rw [hp]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((23 : ℝ) ^ 10) ^ 2)]
  rw [Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (23 : ℝ) ^ 10)]

private theorem cyclotomic_regulator_div_realSubfield_regulator :
    regulator K23 / regulator K23plus =
      (2 : ℝ) ^ 10 * (NumberField.IsCMField.indexRealUnits K23 : ℝ)⁻¹ := by
  simpa [cyclotomic_unitRank] using
    (NumberField.IsCMField.regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv
      K23)

/-- The analytic class-number formula for the maximal real subfield, after
substituting its proved class number, discriminant, signature, and torsion. -/
theorem maximalRealSubfield_dedekindZeta_residue :
    NumberField.dedekindZeta_residue K23plus =
      (2 : ℝ) ^ 10 * regulator K23plus / (23 : ℝ) ^ 5 := by
  rw [NumberField.dedekindZeta_residue_def, realSubfield_nrRealPlaces,
    realSubfield_nrComplexPlaces, realSubfield_torsionOrder,
    maximalRealSubfield_classNumber_eq_one,
    sqrt_abs_maximalRealSubfield_discr]
  norm_num
  ring

/-- The analytic class-number formula for `ℚ(ζ₂₃)`, with its signature,
torsion order, and discriminant evaluated explicitly. -/
theorem cyclotomic_dedekindZeta_residue :
    NumberField.dedekindZeta_residue K23 =
      (2 * Real.pi) ^ 11 * regulator K23 * (NumberField.classNumber K23 : ℝ) /
        (46 * ((23 : ℝ) ^ 10 * Real.sqrt 23)) := by
  rw [NumberField.dedekindZeta_residue_def, cyclotomic_nrRealPlaces,
    cyclotomic_nrComplexPlaces, cyclotomic_torsionOrder,
    sqrt_abs_cyclotomic_discr]
  norm_num

/-- After every known constant is cancelled, the scaled residue ratio is the
cyclotomic class number divided by the Hasse unit index. -/
theorem scaledDedekindZetaResidueRatio_eq_classNumber_div_indexRealUnits :
    (NumberField.dedekindZeta_residue K23 /
        NumberField.dedekindZeta_residue K23plus) *
          ((23 : ℝ) ^ 6 * Real.sqrt 23) /
            ((2 : ℝ) ^ 10 * Real.pi ^ 11) =
      (NumberField.classNumber K23 : ℝ) /
        (NumberField.IsCMField.indexRealUnits K23 : ℝ) := by
  have hreg := cyclotomic_regulator_div_realSubfield_regulator
  have hrK : regulator K23 ≠ 0 := regulator_ne_zero K23
  have hrP : regulator K23plus ≠ 0 := regulator_ne_zero K23plus
  have hsqrt : Real.sqrt (23 : ℝ) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hq : (NumberField.IsCMField.indexRealUnits K23 : ℝ) ≠ 0 := by
    rcases NumberField.IsCMField.indexRealUnits_eq_one_or_two K23 with h | h <;>
      simp [h]
  rw [cyclotomic_dedekindZeta_residue,
    maximalRealSubfield_dedekindZeta_residue]
  field_simp at hreg ⊢
  nlinarith [hreg]

/-- The remaining analytic theorem at `23`.

It packages the absent factorization of the cyclotomic Dedekind zeta function
into odd Dirichlet `L`-functions, their functional equations and special
values, and the finite character-product identification with the resultant.
The proposition is deliberately a definition, not an axiom or theorem. -/
def OddCharacterAnalyticBridgeTwentyThree : Prop :=
  (NumberField.dedekindZeta_residue K23 /
      NumberField.dedekindZeta_residue K23plus) *
        ((23 : ℝ) ^ 6 * Real.sqrt 23) /
          ((2 : ℝ) ^ 10 * Real.pi ^ 11) =
    ((-(oddCharacterRootPolynomial.resultant characterSumPolynomial) /
        (46 : ℚ) ^ 10 : ℚ) : ℝ)

/-- The missing odd-character bridge, if supplied, computes the quotient of
the class number by the Hasse unit index as `3`. -/
theorem classNumber_div_indexRealUnits_eq_three_of_oddCharacterAnalyticBridge
    (hbridge : OddCharacterAnalyticBridgeTwentyThree) :
    (NumberField.classNumber K23 : ℝ) /
        (NumberField.IsCMField.indexRealUnits K23 : ℝ) = 3 := by
  calc
    (NumberField.classNumber K23 : ℝ) /
          (NumberField.IsCMField.indexRealUnits K23 : ℝ) =
        (NumberField.dedekindZeta_residue K23 /
            NumberField.dedekindZeta_residue K23plus) *
              ((23 : ℝ) ^ 6 * Real.sqrt 23) /
                ((2 : ℝ) ^ 10 * Real.pi ^ 11) :=
      scaledDedekindZetaResidueRatio_eq_classNumber_div_indexRealUnits.symm
    _ = ((-(oddCharacterRootPolynomial.resultant characterSumPolynomial) /
          (46 : ℚ) ^ 10 : ℚ) : ℝ) := hbridge
    _ = 3 := by
      norm_cast
      exact normalizedCharacterSumProduct

/-- Thus the analytic bridge alone gives `h = 3Q`, retaining the Hasse unit
index `Q` rather than assuming it is one. -/
theorem classNumber_eq_three_mul_indexRealUnits_of_oddCharacterAnalyticBridge
    (hbridge : OddCharacterAnalyticBridgeTwentyThree) :
    NumberField.classNumber K23 =
      3 * NumberField.IsCMField.indexRealUnits K23 := by
  have hratio :=
    classNumber_div_indexRealUnits_eq_three_of_oddCharacterAnalyticBridge hbridge
  have hq : (NumberField.IsCMField.indexRealUnits K23 : ℝ) ≠ 0 := by
    rcases NumberField.IsCMField.indexRealUnits_eq_one_or_two K23 with h | h <;>
      simp [h]
  have hreal : (NumberField.classNumber K23 : ℝ) =
      3 * (NumberField.IsCMField.indexRealUnits K23 : ℝ) :=
    (div_eq_iff hq).mp hratio
  exact_mod_cast hreal

/-- The proved Hasse unit-index computation removes the final factor `Q`:
the odd-character bridge computes the cyclotomic class number as `3`. -/
theorem classNumber_eq_three_of_oddCharacterAnalyticBridge
    (hbridge : OddCharacterAnalyticBridgeTwentyThree) :
    NumberField.classNumber K23 = 3 := by
  have hclass :=
    classNumber_eq_three_mul_indexRealUnits_of_oddCharacterAnalyticBridge hbridge
  simpa [indexRealUnits_eq_one] using hclass

/-- The odd-character bridge therefore proves that `23` is regular. -/
theorem isRegularPrime_twentyThree_of_oddCharacterAnalyticBridge
    (hbridge : OddCharacterAnalyticBridgeTwentyThree) :
    IsRegularPrime 23 := by
  rw [IsRegularPrime, IsRegularNumber]
  change Nat.Coprime 23 (NumberField.classNumber K23)
  rw [classNumber_eq_three_of_oddCharacterAnalyticBridge hbridge]
  norm_num

/-- The odd-character bridge therefore proves FLT for exponent `23`. -/
theorem fermatLastTheoremTwentyThree_of_oddCharacterAnalyticBridge
    (hbridge : OddCharacterAnalyticBridgeTwentyThree) :
    FermatLastTheoremFor 23 :=
  flt_regular
    (isRegularPrime_twentyThree_of_oddCharacterAnalyticBridge hbridge)
    (by norm_num)

end

end BealRegular.TwentyThreeAnalyticClassNumber
