module

public import BealRegular.TwentyThreeRamifiedPrime
public import Mathlib.NumberTheory.NumberField.CMField

/-!
# The maximal real subfield of Q(zeta_23)

The 23rd cyclotomic field is a CM field, so it is quadratic over its maximal
real subfield.  Since its degree over `ℚ` is `φ(23) = 22`, the maximal real
subfield has degree `11`.  This establishes the field-size reduction used by
the compact real-subfield route; it does not yet identify an explicit power
basis or prove that the real subfield has class number one.
-/

@[expose] public section

open NumberField Polynomial

namespace BealRegular.TwentyThreeRealSubfield

noncomputable section

local notation "K23" => CyclotomicField 23 ℚ
local notation "K23plus" => NumberField.maximalRealSubfield K23

local instance : Fact (Nat.Prime 23) :=
  ⟨BealRegular.TwentyThreePrimeTwoCube.prime_twentyThree⟩
local instance : IsCyclotomicExtension {23} ℚ K23 :=
  CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero 23 ℚ

local instance : NumberField.IsCMField K23 :=
  IsCyclotomicExtension.Rat.isCMField K23 (S := ({23} : Set ℕ))
    ⟨23, by simp, by omega⟩

/-- The 23rd cyclotomic field is a CM field. -/
theorem cyclotomicFieldTwentyThree_isCMField :
    NumberField.IsCMField K23 :=
  inferInstance

/-- The maximal real subfield of `ℚ(ζ₂₃)` has degree eleven over `ℚ`. -/
theorem maximalRealSubfield_finrank :
    Module.finrank ℚ K23plus = 11 := by
  have h := Module.finrank_mul_finrank ℚ K23plus K23
  rw [Algebra.IsQuadraticExtension.finrank_eq_two K23plus K23,
    IsCyclotomicExtension.Rat.finrank 23 K23,
    Nat.totient_prime
      BealRegular.TwentyThreePrimeTwoCube.prime_twentyThree] at h
  omega

/-- The distinguished primitive 23rd root of unity in the cyclotomic field. -/
def zeta23 : K23 :=
  IsCyclotomicExtension.zeta 23 ℚ K23

theorem zeta23_isPrimitiveRoot :
    IsPrimitiveRoot zeta23 23 := by
  simpa only [zeta23] using
    BealRegular.TwentyThreeRamifiedPrime.zeta23_spec

/-- The conventional generator `-(ζ₂₃ + ζ₂₃⁻¹)` before restricting it to the
maximal real subfield. -/
def alphaInCyclotomic : K23 :=
  -(zeta23 + zeta23⁻¹)

theorem alphaInCyclotomic_mem_maximalRealSubfield :
    alphaInCyclotomic ∈ K23plus := by
  rw [NumberField.mem_maximalRealSubfield_iff]
  intro φ
  have hpow : (φ zeta23) ^ 23 = 1 := by
    rw [← map_pow, zeta23_isPrimitiveRoot.pow_eq_one, map_one]
  have hnorm : ‖φ zeta23‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hpow (by norm_num)
  have hinv : (φ zeta23)⁻¹ = star (φ zeta23) := by
    rw [RCLike.star_def]
    exact Complex.inv_eq_conj hnorm
  have hstar_inv : star ((φ zeta23)⁻¹) = φ zeta23 := by
    rw [hinv, star_star]
  simp only [alphaInCyclotomic, map_neg, map_add, map_inv₀]
  rw [star_neg, star_add, ← hinv, hstar_inv]
  exact congrArg Neg.neg (add_comm _ _)

/-- The explicit degree-eleven candidate generator in the maximal real
subfield. -/
def alpha : K23plus :=
  ⟨alphaInCyclotomic, alphaInCyclotomic_mem_maximalRealSubfield⟩

@[simp]
theorem alpha_coe : (alpha : K23) = -(zeta23 + zeta23⁻¹) :=
  rfl

/-- A monic integral defining-polynomial candidate for the real generator. -/
def realSubfieldPolynomial : ℤ[X] :=
  X ^ 11 - X ^ 10 - C 10 * X ^ 9 + C 9 * X ^ 8 + C 36 * X ^ 7 -
    C 28 * X ^ 6 - C 56 * X ^ 5 + C 35 * X ^ 4 + C 35 * X ^ 3 -
      C 15 * X ^ 2 - C 6 * X + C 1

/-- The exact Laurent identity connecting the degree-eleven polynomial to the
23rd cyclotomic geometric sum. -/
theorem zeta23_pow_eleven_mul_aeval_realSubfieldPolynomial :
    zeta23 ^ 11 * aeval alphaInCyclotomic realSubfieldPolynomial =
      -(∑ i ∈ Finset.range 23, zeta23 ^ i) := by
  have hz : zeta23 ≠ 0 := zeta23_isPrimitiveRoot.ne_zero (by norm_num)
  simp only [realSubfieldPolynomial, map_sub, map_add, map_mul, map_pow,
    map_ofNat, map_one, aeval_X, alphaInCyclotomic,
    Finset.sum_range_succ]
  field_simp [hz]
  ring

/-- The primitive root annihilates the 23-term geometric sum. -/
theorem zeta23_geometric_sum_eq_zero :
    (∑ i ∈ Finset.range 23, zeta23 ^ i) = 0 := by
  have hroot := zeta23_isPrimitiveRoot.isRoot_cyclotomic (by norm_num)
  rw [Polynomial.IsRoot.def, Polynomial.cyclotomic_prime K23 23] at hroot
  simpa using hroot

/-- The displayed integral polynomial vanishes at the explicit element in the
full cyclotomic field. -/
theorem aeval_realSubfieldPolynomial_alphaInCyclotomic :
    aeval alphaInCyclotomic realSubfieldPolynomial = 0 := by
  have h := zeta23_pow_eleven_mul_aeval_realSubfieldPolynomial
  rw [zeta23_geometric_sum_eq_zero, neg_zero] at h
  exact (mul_eq_zero.mp h).resolve_left
    (pow_ne_zero 11 (zeta23_isPrimitiveRoot.ne_zero (by norm_num)))

/-- The same polynomial vanishes at `alpha` inside the maximal real subfield. -/
theorem aeval_realSubfieldPolynomial_alpha :
    aeval alpha realSubfieldPolynomial = 0 := by
  apply (algebraMap K23plus K23).injective
  rw [map_zero]
  calc
    algebraMap K23plus K23 (aeval alpha realSubfieldPolynomial) =
        aeval (algebraMap K23plus K23 alpha) realSubfieldPolynomial := by
      simpa only [map_id, Polynomial.map_id] using
        (Polynomial.map_aeval_eq_aeval_map
          (R := ℤ) (φ := RingHom.id ℤ) (ψ := algebraMap K23plus K23)
          (by ext; simp) realSubfieldPolynomial alpha)
    _ = aeval alphaInCyclotomic realSubfieldPolynomial := by rfl
    _ = 0 := aeval_realSubfieldPolynomial_alphaInCyclotomic

end

end BealRegular.TwentyThreeRealSubfield
