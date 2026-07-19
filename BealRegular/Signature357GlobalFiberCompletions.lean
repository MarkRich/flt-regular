import BealRegular.AdjoinRootBaseChange
import BealRegular.Signature357FixedLocalDecomposition
import BealRegular.Signature357LocalRatio

/-!
# P-adic completions of the rational signature `(3,5,7)` fiber

For natural numbers `B` and `C`, this module packages the rational algebra

`K_(B,C) = ℚ[T] / (phi(T) - B^5 / C^7)`

and identifies its scalar extension to every p-adic field with the
corresponding p-adic fiber algebra.  It then connects two divisibility cases
from a coprime signature `(3,5,7)` equation to the explicit nearby-branch
decompositions:

* if `p ∣ B`, the completion is the quadratic model times the quintic model
  with parameter `1 / (21 * C^2)`;
* if `p ∣ A` and `A^3 + B^5 = C^7`, the completion is the quartic model times
  the cubic model with parameter `-1 / (35 * C^4)`.

These are necessary local descriptions of a rational fiber.  A product
decomposition after completion does not imply that the rational algebra has
global factors of the same degrees.  The results do not cover the other local
branches or the exceptional primes `3`, `5`, and `7`, prove unramifiedness,
classify number fields, exclude signature `(3,5,7)`, or prove Beal's
conjecture.
-/

namespace BealRegular.Signature357GlobalFiberCompletions

open scoped Ring TensorProduct

open AdjoinRootBaseChange
open Signature357FixedLocalDecomposition
open Signature357LocalRatio
open Signature357ModelFactorAlgebras
open Signature357ResidualMonicModels

noncomputable section

/-- The rational degree-seven fiber algebra attached to `eta = B^5 / C^7`. -/
abbrev GlobalFiberAlgebra (B C : ℕ) :=
  AdjoinRoot
    (Signature357GenericLocalPolynomial.fiberK (K := ℚ) (eta B C))

/-- Scalar extension of the rational fiber to `ℚ_[p]` is the p-adic fiber at
the image of the same rational parameter. -/
def globalFiberBaseChangePadicAlgEquiv (p B C : ℕ) [Fact p.Prime] :
    (ℚ_[p] ⊗[ℚ] (GlobalFiberAlgebra B C)) ≃ₐ[ℚ_[p]]
      AdjoinRoot
        (Signature357GenericLocalPolynomial.fiberK
          (K := ℚ_[p]) (algebraMap ℚ ℚ_[p] (eta B C))) := by
  rw [← Signature357GenericLocalPolynomial.fiberK_map
    (algebraMap ℚ ℚ_[p]) (eta B C)]
  exact adjoinRootBaseChangeAlgEquiv (S := ℚ_[p])
    (Signature357GenericLocalPolynomial.fiberK (K := ℚ) (eta B C))

private theorem natCast_isUnit_of_not_dvd
    {p n : ℕ} [Fact p.Prime] (hn : ¬p ∣ n) :
    IsUnit (n : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hn

private theorem natCast_mem_padicIdeal_of_dvd
    {p n : ℕ} [Fact p.Prime] (hn : p ∣ n) :
    (n : ℤ_[p]) ∈ padicIdeal (p := p) := by
  rw [padicIdeal, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd,
    PadicInt.norm_natCast_lt_one_iff]
  exact hn

private theorem algebraMap_ringInverse_natCast
    {p n : ℕ} [Fact p.Prime] (hn : IsUnit (n : ℤ_[p])) :
    algebraMap ℤ_[p] ℚ_[p] ((n : ℤ_[p])⁻¹ʳ) = (n : ℚ_[p])⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  change
    algebraMap ℤ_[p] ℚ_[p] ((n : ℤ_[p])⁻¹ʳ) *
      algebraMap ℤ_[p] ℚ_[p] (n : ℤ_[p]) = 1
  rw [← map_mul, Ring.inverse_mul_cancel _ hn, map_one]

/-- If the p-adic parameter has zero-branch form `q^5 * a`, the completion of
the rational fiber has the explicit quadratic-by-quintic decomposition. -/
theorem globalFiberCompletion_zeroBranch
    {p B C : ℕ} [Fact p.Prime]
    (q a : ℤ_[p]) (ha : IsUnit a) (hq : q ≠ 0)
    (hqI : q ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (heta : algebraMap ℚ ℚ_[p] (eta B C) =
      algebraMap ℤ_[p] ℚ_[p] (q ^ 5 * a)) :
    Nonempty
      ((ℚ_[p] ⊗[ℚ] (GlobalFiberAlgebra B C)) ≃ₐ[ℚ_[p]]
        QuadraticFactorAlgebra (K := ℚ_[p]) ×
          BinomialModelAlgebra 5
            (algebraMap ℤ_[p] ℚ_[p] ((21 : ℤ_[p])⁻¹ʳ * a))) := by
  obtain ⟨hlocal⟩ := zeroBranch_fixedModel_padicDecomposition
    q a ha hq hqI hp3 hp5 hp7
  refine ⟨(globalFiberBaseChangePadicAlgEquiv p B C).trans ?_⟩
  rw [heta]
  exact hlocal

/-- If the p-adic parameter has translated-one form `1 + q^3 * a`, the
completion of the rational fiber has the explicit quartic-by-cubic
decomposition. -/
theorem globalFiberCompletion_oneBranch
    {p B C : ℕ} [Fact p.Prime]
    (q a : ℤ_[p]) (ha : IsUnit a) (hq : q ≠ 0)
    (hqI : q ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (heta : algebraMap ℚ ℚ_[p] (eta B C) =
      algebraMap ℤ_[p] ℚ_[p] (1 + q ^ 3 * a)) :
    Nonempty
      ((ℚ_[p] ⊗[ℚ] (GlobalFiberAlgebra B C)) ≃ₐ[ℚ_[p]]
        QuarticFactorAlgebra (K := ℚ_[p]) ×
          BinomialModelAlgebra 3
            (algebraMap ℤ_[p] ℚ_[p] ((35 : ℤ_[p])⁻¹ʳ * a))) := by
  obtain ⟨hlocal⟩ := oneBranch_fixedModel_padicDecomposition
    q a ha hq hqI hp3 hp5 hp7
  refine ⟨(globalFiberBaseChangePadicAlgEquiv p B C).trans ?_⟩
  rw [heta]
  exact hlocal

/-- A prime dividing the numerator `B` puts the completion of the rational
fiber on the quadratic-by-quintic branch.  Coprimality makes `C` a p-adic
unit, and the branch parameters are `q = B / C` and `a = C⁻²`. -/
theorem globalFiberCompletion_of_prime_dvd_B
    {p B C : ℕ} [Fact p.Prime]
    (hB : B ≠ 0) (hBC : Nat.Coprime B C)
    (hpB : p ∣ B)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    Nonempty
      ((ℚ_[p] ⊗[ℚ] (GlobalFiberAlgebra B C)) ≃ₐ[ℚ_[p]]
        QuadraticFactorAlgebra (K := ℚ_[p]) ×
          BinomialModelAlgebra 5
            (algebraMap ℤ_[p] ℚ_[p]
              ((21 : ℤ_[p])⁻¹ʳ * ((C : ℤ_[p])⁻¹ʳ) ^ 2))) := by
  have hpC : ¬p ∣ C := by
    have hpc : Nat.Coprime p C := Nat.Coprime.of_dvd_left hpB hBC
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hpc
  have hCunit : IsUnit (C : ℤ_[p]) := natCast_isUnit_of_not_dvd hpC
  let q : ℤ_[p] := (B : ℤ_[p]) * (C : ℤ_[p])⁻¹ʳ
  let a : ℤ_[p] := ((C : ℤ_[p])⁻¹ʳ) ^ 2
  have ha : IsUnit a := by
    exact hCunit.ringInverse.pow 2
  have hq : q ≠ 0 := by
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hB)
      hCunit.ringInverse.ne_zero
  have hBI : (B : ℤ_[p]) ∈ padicIdeal (p := p) :=
    natCast_mem_padicIdeal_of_dvd hpB
  have hqI : q ∈ padicIdeal (p := p) :=
    (padicIdeal (p := p)).mul_mem_right (C : ℤ_[p])⁻¹ʳ hBI
  have hCmap := algebraMap_ringInverse_natCast (p := p) hCunit
  have hratio : algebraMap ℤ_[p] ℚ_[p] (q ^ 5 * a) =
      (B : ℚ_[p]) ^ 5 / (C : ℚ_[p]) ^ 7 := by
    simp only [map_pow, map_natCast, map_mul, q, a]
    rw [hCmap]
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  have hetaCast : ((eta B C : ℚ) : ℚ_[p]) =
      (B : ℚ_[p]) ^ 5 / (C : ℚ_[p]) ^ 7 := by
    simp [eta]
  have heta : algebraMap ℚ ℚ_[p] (eta B C) =
      algebraMap ℤ_[p] ℚ_[p] (q ^ 5 * a) := by
    change ((eta B C : ℚ) : ℚ_[p]) = _
    exact hetaCast.trans hratio.symm
  simpa only [a] using globalFiberCompletion_zeroBranch
    q a ha hq hqI hp3 hp5 hp7 heta

/-- For a signature `(3,5,7)` equation, a prime dividing `A` puts the
completion on the quartic-by-cubic branch.  Here `q = A / C` and
`a = -C⁻⁴`. -/
theorem globalFiberCompletion_of_prime_dvd_A
    {p A B C : ℕ} [Fact p.Prime]
    (hA : A ≠ 0) (hAC : Nat.Coprime A C) (hpA : p ∣ A)
    (hEq : A ^ 3 + B ^ 5 = C ^ 7)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    Nonempty
      ((ℚ_[p] ⊗[ℚ] (GlobalFiberAlgebra B C)) ≃ₐ[ℚ_[p]]
        QuarticFactorAlgebra (K := ℚ_[p]) ×
          BinomialModelAlgebra 3
            (algebraMap ℤ_[p] ℚ_[p]
              ((35 : ℤ_[p])⁻¹ʳ * -((C : ℤ_[p])⁻¹ʳ) ^ 4))) := by
  have hpC : ¬p ∣ C := by
    have hpc : Nat.Coprime p C := Nat.Coprime.of_dvd_left hpA hAC
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hpc
  have hCunit : IsUnit (C : ℤ_[p]) := natCast_isUnit_of_not_dvd hpC
  let q : ℤ_[p] := (A : ℤ_[p]) * (C : ℤ_[p])⁻¹ʳ
  let a : ℤ_[p] := -((C : ℤ_[p])⁻¹ʳ) ^ 4
  have ha : IsUnit a := by
    exact (hCunit.ringInverse.pow 4).neg
  have hq : q ≠ 0 := by
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hA)
      hCunit.ringInverse.ne_zero
  have hAI : (A : ℤ_[p]) ∈ padicIdeal (p := p) :=
    natCast_mem_padicIdeal_of_dvd hpA
  have hqI : q ∈ padicIdeal (p := p) :=
    (padicIdeal (p := p)).mul_mem_right (C : ℤ_[p])⁻¹ʳ hAI
  have hCmap := algebraMap_ringInverse_natCast (p := p) hCunit
  have hbranch : algebraMap ℤ_[p] ℚ_[p] (1 + q ^ 3 * a) =
      1 - (A : ℚ_[p]) ^ 3 / (C : ℚ_[p]) ^ 7 := by
    simp only [map_add, map_one, map_mul, map_pow, map_natCast, map_neg,
      q, a]
    rw [hCmap, div_eq_mul_inv, ← inv_pow]
    ring
  have hC : C ≠ 0 := by
    intro hC0
    apply hpC
    simp [hC0]
  have hetaQ : eta B C = 1 - (A : ℚ) ^ 3 / (C : ℚ) ^ 7 := by
    linarith [one_sub_eta_eq hC hEq]
  have hetaCast : ((eta B C : ℚ) : ℚ_[p]) =
      1 - (A : ℚ_[p]) ^ 3 / (C : ℚ_[p]) ^ 7 := by
    rw [hetaQ]
    norm_num
  have heta : algebraMap ℚ ℚ_[p] (eta B C) =
      algebraMap ℤ_[p] ℚ_[p] (1 + q ^ 3 * a) := by
    change ((eta B C : ℚ) : ℚ_[p]) = _
    exact hetaCast.trans hbranch.symm
  simpa only [a] using globalFiberCompletion_oneBranch
    q a ha hq hqI hp3 hp5 hp7 heta

end

end BealRegular.Signature357GlobalFiberCompletions
