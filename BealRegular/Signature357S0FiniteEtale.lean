import BealRegular.AdjoinRootBaseChange
import BealRegular.AdjoinRootEtale
import BealRegular.Signature357AdicFactorLifting
import BealRegular.Signature357GlobalFiberCompletions
import BealRegular.Signature357PadicModelUnits
import BealRegular.Signature357ResidualMonicModels
import Mathlib.RingTheory.Unramified.Locus

/-!
# Finite-etale models on the signature `(3,5,7)` ordinary branch

For a p-adic integral parameter `u`, the normalized degree-seven fiber has
derivative

`7 * X^4 * (X - 1)^2`.

Consequently, away from `3`, `5`, and `7`, the unit conditions on `u` and
`1 - u` make the fiber coprime to its derivative.  This module turns that
observation into a unit-discriminant theorem and an explicit finite-etale
integral model over `ℤ_[p]`.

For a solution `A^3 + B^5 = C^7`, a prime dividing none of `A`, `B`, and `C`
gives precisely those two unit conditions for the integral parameter
`B^5 * C⁻⁷`.  The final theorem identifies the p-adic completion of the
global rational fiber with the generic fiber of this finite-etale model.

These results prove good reduction at an ordinary prime.  They do not handle
the exceptional primes `3`, `5`, or `7`, determine the factorization of the
completion, identify global number fields or their rings of integers, prove a
global discriminant bound, exclude signature `(3,5,7)`, or prove Beal's
conjecture.
-/

namespace BealRegular.Signature357S0FiniteEtale

open Polynomial
open scoped Ring TensorProduct

open AdjoinRootBaseChange
open AdjoinRootEtale
open Signature357GenericLocalPolynomial
open Signature357GlobalFiberCompletions
open Signature357LocalRatio
open Signature357PadicModelUnits
open Signature357AdicFactorLifting
open Signature357ResidualMonicModels

noncomputable section

variable {p : ℕ} [Fact p.Prime]

private theorem natCast_isUnit_of_not_dvd {n : ℕ} (hn : ¬p ∣ n) :
    IsUnit (n : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hn

private theorem algebraMap_ringInverse_natCast
    {n : ℕ} (hn : IsUnit (n : ℤ_[p])) :
    algebraMap ℤ_[p] ℚ_[p] ((n : ℤ_[p])⁻¹ʳ) = (n : ℚ_[p])⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  change
    algebraMap ℤ_[p] ℚ_[p] ((n : ℤ_[p])⁻¹ʳ) *
      algebraMap ℤ_[p] ℚ_[p] (n : ℤ_[p]) = 1
  rw [← map_mul, Ring.inverse_mul_cancel _ hn, map_one]

private theorem fifteen_isUnit
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    IsUnit (15 : ℤ_[p]) := by
  obtain ⟨h15, -⟩ := quadraticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  simpa only [quadraticIntegralModel_leadingCoeff] using h15

private theorem seven_isUnit (hp7 : p ≠ 7) : IsUnit (7 : ℤ_[p]) := by
  apply natCast_isUnit_of_not_dvd
  intro hp7dvd
  exact hp7 <|
    (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_seven).mp hp7dvd

/-- A unit value at `a` makes a polynomial coprime to `X - a`. -/
private theorem isCoprime_X_sub_C_of_eval_isUnit
    {R : Type*} [CommRing R] (f : R[X]) (a : R)
    (h : IsUnit (f.eval a)) : IsCoprime f (X - C a) := by
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (p := f) (a := a)
  obtain ⟨u, hu⟩ := h
  rw [← hu] at hq
  have hsplit : f = (X - C a) * q + C ((↑u : R)) :=
    eq_add_of_sub_eq hq
  refine ⟨C ((↑(u⁻¹) : R)), -(C ((↑(u⁻¹) : R)) * q), ?_⟩
  rw [hsplit]
  simp only [mul_add, neg_mul]
  calc
    C ((↑(u⁻¹) : R)) * ((X - C a) * q) +
          C ((↑(u⁻¹) : R)) * C ((↑u : R)) -
          C ((↑(u⁻¹) : R)) * q * (X - C a) =
        C ((↑(u⁻¹) : R)) * C ((↑u : R)) := by ring
    _ = 1 := by rw [← C_mul]; simp

/-- The normalized integral fiber has the same critical points `0` and `1`
as the characteristic-zero fiber. -/
theorem normalizedIntegralFiber_derivative
    (u : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (normalizedIntegralFiber u).derivative =
      C (7 : ℤ_[p]) * (X ^ 4 * (X - C 1) ^ 2) := by
  have h15 := fifteen_isUnit hp3 hp5 hp7
  have hcancel : (15 : ℤ_[p])⁻¹ʳ * 15 = 1 :=
    Ring.inverse_mul_cancel _ h15
  have hcancelC :
      (C ((15 : ℤ_[p])⁻¹ʳ) : ℤ_[p][X]) * 15 = 1 := by
    simpa only [C_mul, C_1, C_ofNat] using congrArg C hcancel
  simp [normalizedIntegralFiber, integralFiber]
  simp only [C_ofNat]
  linear_combination
    (7 * X ^ 6 - 14 * X ^ 5 + 7 * X ^ 4 : ℤ_[p][X]) * hcancelC

/-- The constant value of the normalized fiber is `-15⁻¹u`. -/
theorem normalizedIntegralFiber_eval_zero
    (u : ℤ_[p]) :
    (normalizedIntegralFiber u).eval 0 = -((15 : ℤ_[p])⁻¹ʳ * u) := by
  simp [normalizedIntegralFiber, integralFiber]

/-- The value of the normalized fiber at one is `15⁻¹(1-u)`. -/
theorem normalizedIntegralFiber_eval_one
    (u : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (normalizedIntegralFiber u).eval 1 =
      (15 : ℤ_[p])⁻¹ʳ * (1 - u) := by
  have h15 := fifteen_isUnit hp3 hp5 hp7
  have hcancel : (15 : ℤ_[p])⁻¹ʳ * 15 = 1 :=
    Ring.inverse_mul_cancel _ h15
  rw [normalizedIntegralFiber, eval_mul, eval_C]
  simp only [integralFiber, eval_sub, eval_add]
  norm_num

/-- If both the parameter and its complement are units, the normalized fiber
is coprime to its derivative over the p-adic integers. -/
theorem normalizedIntegralFiber_isCoprime_derivative
    (u : ℤ_[p]) (hu : IsUnit u) (h1u : IsUnit (1 - u))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    IsCoprime (normalizedIntegralFiber u)
      (normalizedIntegralFiber u).derivative := by
  let P := normalizedIntegralFiber (p := p) u
  have h15 := fifteen_isUnit hp3 hp5 hp7
  have hP0 : IsUnit (P.coeff 0) := by
    have heval : IsUnit (P.eval 0) := by
      rw [normalizedIntegralFiber_eval_zero]
      exact (h15.ringInverse.mul hu).neg
    simpa [coeff_zero_eq_eval_zero] using heval
  have hPX4 : IsCoprime P (X ^ 4) :=
    isCoprime_X_pow_of_coeff_zero_isUnit P hP0 4
  have hP1 : IsUnit (P.eval 1) := by
    rw [normalizedIntegralFiber_eval_one u hp3 hp5 hp7]
    exact h15.ringInverse.mul h1u
  have hPX1 : IsCoprime P (X - C 1) := by
    exact isCoprime_X_sub_C_of_eval_isUnit P 1 hP1
  have hcritical : IsCoprime P (X ^ 4 * (X - C 1) ^ 2) :=
    hPX4.mul_right hPX1.pow_right
  rw [normalizedIntegralFiber_derivative u hp3 hp5 hp7]
  exact (isCoprime_mul_unit_left_right
    ((seven_isUnit hp7).map C) P (X ^ 4 * (X - C 1) ^ 2)).mpr hcritical

/-- Equivalently, the monic integral fiber has unit polynomial
discriminant.  This is the arithmetic good-reduction certificate used by the
finite-etale theorem below. -/
theorem normalizedIntegralFiber_discr_isUnit
    (u : ℤ_[p]) (hu : IsUnit u) (h1u : IsUnit (1 - u))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    IsUnit (normalizedIntegralFiber u).discr := by
  let P := normalizedIntegralFiber (p := p) u
  have hPmonic : P.Monic :=
    normalizedIntegralFiber_monic u hp3 hp5 hp7
  have hPdeg : P.natDegree = 7 :=
    normalizedIntegralFiber_natDegree u hp3 hp5 hp7
  have hcop : IsCoprime P P.derivative :=
    normalizedIntegralFiber_isCoprime_derivative
      u hu h1u hp3 hp5 hp7
  have hres : IsUnit (P.resultant P.derivative) :=
    (isUnit_resultant_iff_isCoprime hPmonic).mpr hcop
  have hle : P.derivative.natDegree ≤ P.natDegree - 1 :=
    natDegree_derivative_le P
  have hsum :
      P.derivative.natDegree +
          ((P.natDegree - 1) - P.derivative.natDegree) =
        P.natDegree - 1 := by omega
  have hres_eq :
      P.resultant P.derivative P.natDegree (P.natDegree - 1) =
        P.resultant P.derivative := by
    rw [← hsum, resultant_add_right_deg _ _ _ _ _ le_rfl]
    simp [hPmonic.leadingCoeff]
  have hdegree : 0 < P.degree := by
    rw [← natDegree_pos_iff_degree_pos, hPdeg]
    norm_num
  have hr := resultant_deriv hdegree
  rw [hres_eq] at hr
  rw [hr, hPmonic.leadingCoeff, mul_one, IsUnit.mul_iff] at hres
  exact hres.2

/-- The `S₀` unit conditions produce a finite-etale integral model over
`ℤ_[p]`.  This is stronger than mere etaleness after passing to `ℚ_[p]`. -/
theorem normalizedIntegralFiber_finiteEtale
    (u : ℤ_[p]) (hu : IsUnit u) (h1u : IsUnit (1 - u))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    Module.Finite ℤ_[p] (AdjoinRoot (normalizedIntegralFiber u)) ∧
      Algebra.Etale ℤ_[p] (AdjoinRoot (normalizedIntegralFiber u)) :=
  adjoinRoot_finiteEtale_of_monic_isCoprime
    (normalizedIntegralFiber u)
    (normalizedIntegralFiber_monic u hp3 hp5 hp7)
    (normalizedIntegralFiber_isCoprime_derivative
      u hu h1u hp3 hp5 hp7)

/-- Consequently every prime of the integral model lying over `(p)` is
unramified in Mathlib's commutative-algebra sense. -/
theorem normalizedIntegralFiber_isUnramifiedIn_padicIdeal
    (u : ℤ_[p]) (hu : IsUnit u) (h1u : IsUnit (1 - u))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    Algebra.IsUnramifiedIn (AdjoinRoot (normalizedIntegralFiber u))
      (padicIdeal (p := p)) := by
  have hEtale := (normalizedIntegralFiber_finiteEtale
    u hu h1u hp3 hp5 hp7).2
  letI : Algebra.Etale ℤ_[p] (AdjoinRoot (normalizedIntegralFiber u)) := hEtale
  haveI : Algebra.FormallyUnramified ℤ_[p]
      (AdjoinRoot (normalizedIntegralFiber u)) := inferInstance
  intro P hP _
  exact (Algebra.formallyUnramified_iff_forall.mp
    (inferInstance : Algebra.FormallyUnramified ℤ_[p]
      (AdjoinRoot (normalizedIntegralFiber u)))) ⟨P, hP⟩

/-- The canonical integral representative of `eta = B⁵/C⁷` on `S₀`. -/
def s0IntegralParameter (B C : ℕ) : ℤ_[p] :=
  (B : ℤ_[p]) ^ 5 * ((C : ℤ_[p])⁻¹ʳ) ^ 7

/-- The `S₀` numerator and denominator conditions make the integral
representative of `eta` a p-adic unit. -/
theorem s0IntegralParameter_isUnit {B C : ℕ}
    (hpB : ¬p ∣ B) (hpC : ¬p ∣ C) :
    IsUnit (s0IntegralParameter (p := p) B C) := by
  exact ((natCast_isUnit_of_not_dvd hpB).pow 5).mul
    ((natCast_isUnit_of_not_dvd hpC).ringInverse.pow 7)

/-- On a signature solution, the complementary parameter is the integral
unit `A³/C⁷`. -/
theorem one_sub_s0IntegralParameter_eq
    {A B C : ℕ}
    (hpC : ¬p ∣ C) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    1 - s0IntegralParameter (p := p) B C =
      (A : ℤ_[p]) ^ 3 * ((C : ℤ_[p])⁻¹ʳ) ^ 7 := by
  have hCunit : IsUnit (C : ℤ_[p]) := natCast_isUnit_of_not_dvd hpC
  have hEqZ : (A : ℤ_[p]) ^ 3 + (B : ℤ_[p]) ^ 5 =
      (C : ℤ_[p]) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ ↦ (n : ℤ_[p])) hEq
  have hEqMul := congrArg
    (fun z : ℤ_[p] ↦ z * ((C : ℤ_[p])⁻¹ʳ) ^ 7) hEqZ
  rw [← mul_pow, Ring.mul_inverse_cancel _ hCunit, one_pow] at hEqMul
  dsimp only [s0IntegralParameter]
  rw [← hEqMul]
  ring

/-- Hence `1 - eta` is also a p-adic unit on `S₀`. -/
theorem one_sub_s0IntegralParameter_isUnit
    {A B C : ℕ}
    (hpA : ¬p ∣ A) (hpC : ¬p ∣ C)
    (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    IsUnit (1 - s0IntegralParameter (p := p) B C) := by
  rw [one_sub_s0IntegralParameter_eq hpC hEq]
  exact ((natCast_isUnit_of_not_dvd hpA).pow 3).mul
    ((natCast_isUnit_of_not_dvd hpC).ringInverse.pow 7)

/-- The complementary integral parameter maps to the rational ratio
`A³/C⁷` in the p-adic field. -/
theorem algebraMap_one_sub_s0IntegralParameter
    {A B C : ℕ}
    (hpC : ¬p ∣ C) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    algebraMap ℤ_[p] ℚ_[p]
        (1 - s0IntegralParameter (p := p) B C) =
      (A : ℚ_[p]) ^ 3 / (C : ℚ_[p]) ^ 7 := by
  rw [one_sub_s0IntegralParameter_eq hpC hEq]
  have hCunit : IsUnit (C : ℤ_[p]) := natCast_isUnit_of_not_dvd hpC
  have hCmap := algebraMap_ringInverse_natCast hCunit
  simp only [map_mul, map_pow, map_natCast]
  rw [hCmap, div_eq_mul_inv, ← inv_pow]

/-- The canonical integral representative maps to the rational local ratio in
the p-adic field. -/
theorem algebraMap_s0IntegralParameter
    {B C : ℕ} (hpC : ¬p ∣ C) :
    algebraMap ℤ_[p] ℚ_[p] (s0IntegralParameter (p := p) B C) =
      algebraMap ℚ ℚ_[p] (eta B C) := by
  have hCunit : IsUnit (C : ℤ_[p]) := natCast_isUnit_of_not_dvd hpC
  have hC0 : C ≠ 0 := by
    intro hC
    apply hpC
    simp [hC]
  have hCmap := algebraMap_ringInverse_natCast hCunit
  change
    algebraMap ℤ_[p] ℚ_[p]
        ((B : ℤ_[p]) ^ 5 * ((C : ℤ_[p])⁻¹ʳ) ^ 7) =
      algebraMap ℚ ℚ_[p] ((B : ℚ) ^ 5 / (C : ℚ) ^ 7)
  simp only [map_mul, map_pow, map_natCast]
  rw [hCmap, div_eq_mul_inv, ← inv_pow]
  norm_num

/-- The generic fiber of the normalized integral model is the original
p-adic fiber algebra. -/
def normalizedIntegralFiberGenericFiberEquiv
    (u : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (ℚ_[p] ⊗[ℤ_[p]] AdjoinRoot (normalizedIntegralFiber u)) ≃ₐ[ℚ_[p]]
      AdjoinRoot (fiberK (algebraMap ℤ_[p] ℚ_[p] u)) := by
  have hunit : IsUnit (C (15 : ℚ_[p])⁻¹ : ℚ_[p][X]) := by
    rw [isUnit_C, isUnit_iff_ne_zero]
    exact inv_ne_zero (by norm_num)
  have hassoc : Associated
      ((normalizedIntegralFiber u).map (algebraMap ℤ_[p] ℚ_[p]))
      (fiberK (algebraMap ℤ_[p] ℚ_[p] u)) := by
    rw [normalizedIntegralFiber_map_padic u hp3 hp5 hp7]
    exact associated_unit_mul_left _ _ hunit
  exact (adjoinRootBaseChangeAlgEquiv
    (S := ℚ_[p]) (normalizedIntegralFiber u)).trans
      (AdjoinRoot.algEquivOfAssociated ℚ_[p] _ _ hassoc)

/-- Strong `S₀` endpoint: the completion of the global fiber is the generic
fiber of an explicit finite-etale `ℤ_[p]`-algebra, and `(p)` is unramified in
that integral model. -/
theorem globalFiberCompletion_s0_hasFiniteEtaleModel
    {A B C : ℕ}
    (hpA : ¬p ∣ A) (hpB : ¬p ∣ B) (hpC : ¬p ∣ C)
    (hEq : A ^ 3 + B ^ 5 = C ^ 7)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (Module.Finite ℤ_[p]
        (AdjoinRoot
          (normalizedIntegralFiber (s0IntegralParameter (p := p) B C))) ∧
      Algebra.Etale ℤ_[p]
        (AdjoinRoot
          (normalizedIntegralFiber (s0IntegralParameter (p := p) B C)))) ∧
    Algebra.IsUnramifiedIn
      (AdjoinRoot
        (normalizedIntegralFiber (s0IntegralParameter (p := p) B C)))
      (padicIdeal (p := p)) ∧
    Nonempty
      ((ℚ_[p] ⊗[ℚ] GlobalFiberAlgebra B C) ≃ₐ[ℚ_[p]]
        (ℚ_[p] ⊗[ℤ_[p]]
          AdjoinRoot
            (normalizedIntegralFiber
              (s0IntegralParameter (p := p) B C)))) := by
  let u := s0IntegralParameter (p := p) B C
  have hu : IsUnit u := s0IntegralParameter_isUnit hpB hpC
  have h1u : IsUnit (1 - u) :=
    one_sub_s0IntegralParameter_isUnit hpA hpC hEq
  have hFE := normalizedIntegralFiber_finiteEtale
    u hu h1u hp3 hp5 hp7
  refine ⟨hFE, normalizedIntegralFiber_isUnramifiedIn_padicIdeal
    u hu h1u hp3 hp5 hp7, ⟨?_⟩⟩
  have heta := algebraMap_s0IntegralParameter
    (p := p) (B := B) (C := C) hpC
  exact (globalFiberBaseChangePadicAlgEquiv p B C).trans <| by
    rw [← heta]
    exact (normalizedIntegralFiberGenericFiberEquiv
      u hp3 hp5 hp7).symm

end

end BealRegular.Signature357S0FiniteEtale
