import BealRegular.Signature357ModelFactorInvariants
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Integral p-adic units for the signature `(3,5,7)` model factors

This module realizes the quadratic `psi`, quartic `Psi`, and normalized
binomial model factors over `ℤ_[p]`.  Away from the relevant small primes it
proves that the fixed endpoint coefficients and discriminants are p-adic
units.  A generic theorem gives the same conclusion for `X^n - a` when `a`
is a unit and `p ∤ n`.

These are integral-model arithmetic inputs to the Dahmen--Siksek local
argument.  They do not lift or identify factors of a nearby fiber, prove
structural stability or a Newton-polygon theorem, construct a quotient-product
isomorphism, deduce the rootwise derivative norm bound `μ = 1` from the unit
discriminants, classify valuation-theoretic ramification, exclude signature
`(3,5,7)`, or prove Beal.
-/

namespace BealRegular.Signature357PadicModelUnits

open Polynomial

open Signature357BranchNormalForms
open Signature357ModelFactorInvariants

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- The quadratic integral model over the p-adic integers. -/
abbrev quadraticIntegralModel : ℤ_[p][X] := psiK

/-- The quartic integral model over the p-adic integers. -/
abbrev quarticIntegralModel : ℤ_[p][X] := PsiK

/-- The normalized integral binomial model `X^n - a`. -/
def binomialIntegralModel (n : ℕ) (a : ℤ_[p]) : ℤ_[p][X] :=
  X ^ n - C a

/-- The quadratic integral model has degree two. -/
theorem quadraticIntegralModel_natDegree :
    (quadraticIntegralModel (p := p)).natDegree = 2 :=
  psiK_natDegree

/-- The leading coefficient of the quadratic integral model is `15`. -/
theorem quadraticIntegralModel_leadingCoeff :
    (quadraticIntegralModel (p := p)).leadingCoeff = 15 := by
  rw [leadingCoeff, quadraticIntegralModel_natDegree]
  simp [quadraticIntegralModel, psiK, coeff_X]

/-- The constant coefficient of the quadratic integral model is `21`. -/
theorem quadraticIntegralModel_coeff_zero :
    (quadraticIntegralModel (p := p)).coeff 0 = 21 := by
  simp [quadraticIntegralModel, psiK]

/-- The quartic integral model has degree four. -/
theorem quarticIntegralModel_natDegree :
    (quarticIntegralModel (p := p)).natDegree = 4 :=
  PsiK_natDegree

/-- The leading coefficient of the quartic integral model is `15`. -/
theorem quarticIntegralModel_leadingCoeff :
    (quarticIntegralModel (p := p)).leadingCoeff = 15 := by
  rw [leadingCoeff, quarticIntegralModel_natDegree]
  simp [quarticIntegralModel, PsiK, coeff_X]

/-- The constant coefficient of the quartic integral model is `35`. -/
theorem quarticIntegralModel_coeff_zero :
    (quarticIntegralModel (p := p)).coeff 0 = 35 := by
  simp [quarticIntegralModel, PsiK]

/-- The quadratic integral model has discriminant `-35`. -/
theorem quadraticIntegralModel_discr :
    (quadraticIntegralModel (p := p)).discr = -35 :=
  psiK_discr

/-- The quartic integral model has discriminant `3^3 * 5^2 * 7^3`. -/
theorem quarticIntegralModel_discr :
    (quarticIntegralModel (p := p)).discr = 3 ^ 3 * 5 ^ 2 * 7 ^ 3 :=
  PsiK_discr

private theorem coprime105_of_ne
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) : p.Coprime 105 := by
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro h
  rw [show 105 = 3 * (5 * 7) by norm_num] at h
  rcases (Fact.out : p.Prime).dvd_mul.mp h with h3 | h57
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h3)
  · rcases (Fact.out : p.Prime).dvd_mul.mp h57 with h5 | h7
    · exact hp5 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_five).mp h5)
    · exact hp7 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_seven).mp h7)

private theorem natCast_isUnit_of_coprime (n : ℕ) (hpn : p.Coprime n) :
    IsUnit (n : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact hpn

private theorem coprime35_of_ne (hp5 : p ≠ 5) (hp7 : p ≠ 7) : p.Coprime 35 := by
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro h
  rw [show 35 = 5 * 7 by norm_num] at h
  rcases (Fact.out : p.Prime).dvd_mul.mp h with h5 | h7
  · exact hp5 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_five).mp h5)
  · exact hp7 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_seven).mp h7)

/-- Away from `3`, `5`, and `7`, both endpoint coefficients of `psi` are
units in the p-adic integers. -/
theorem quadraticIntegralModel_endpoints_isUnit
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    IsUnit (quadraticIntegralModel (p := p)).leadingCoeff ∧
      IsUnit ((quadraticIntegralModel (p := p)).coeff 0) := by
  rw [quadraticIntegralModel_leadingCoeff, quadraticIntegralModel_coeff_zero]
  have h105 := coprime105_of_ne hp3 hp5 hp7
  exact ⟨natCast_isUnit_of_coprime 15 (h105.of_dvd_right (by norm_num)),
    natCast_isUnit_of_coprime 21 (h105.of_dvd_right (by norm_num))⟩

/-- Away from `3`, `5`, and `7`, both endpoint coefficients of `Psi` are
units in the p-adic integers. -/
theorem quarticIntegralModel_endpoints_isUnit
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    IsUnit (quarticIntegralModel (p := p)).leadingCoeff ∧
      IsUnit ((quarticIntegralModel (p := p)).coeff 0) := by
  rw [quarticIntegralModel_leadingCoeff, quarticIntegralModel_coeff_zero]
  have h105 := coprime105_of_ne hp3 hp5 hp7
  exact ⟨natCast_isUnit_of_coprime 15 (h105.of_dvd_right (by norm_num)),
    natCast_isUnit_of_coprime 35 (h105.of_dvd_right (by norm_num))⟩

/-- The endpoint norms of `psi` are one away from `3`, `5`, and `7`. -/
theorem quadraticIntegralModel_endpoint_norms
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    ‖(quadraticIntegralModel (p := p)).leadingCoeff‖ = 1 ∧
      ‖(quadraticIntegralModel (p := p)).coeff 0‖ = 1 := by
  obtain ⟨hl, hc⟩ := quadraticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  exact ⟨PadicInt.isUnit_iff.mp hl, PadicInt.isUnit_iff.mp hc⟩

/-- The endpoint norms of `Psi` are one away from `3`, `5`, and `7`. -/
theorem quarticIntegralModel_endpoint_norms
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    ‖(quarticIntegralModel (p := p)).leadingCoeff‖ = 1 ∧
      ‖(quarticIntegralModel (p := p)).coeff 0‖ = 1 := by
  obtain ⟨hl, hc⟩ := quarticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  exact ⟨PadicInt.isUnit_iff.mp hl, PadicInt.isUnit_iff.mp hc⟩

/-- The discriminant of `psi` is a p-adic unit away from `5` and `7`. -/
theorem quadraticIntegralModel_discr_isUnit (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    IsUnit (quadraticIntegralModel (p := p)).discr := by
  rw [quadraticIntegralModel_discr]
  rw [PadicInt.isUnit_iff, norm_neg]
  change ‖((35 : ℕ) : ℤ_[p])‖ = 1
  rw [PadicInt.norm_natCast_eq_one_iff]
  exact coprime35_of_ne hp5 hp7

/-- The discriminant of `Psi` is a p-adic unit away from `3`, `5`, and `7`. -/
theorem quarticIntegralModel_discr_isUnit
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    IsUnit (quarticIntegralModel (p := p)).discr := by
  rw [quarticIntegralModel_discr, PadicInt.isUnit_iff]
  have heq : (3 ^ 3 * 5 ^ 2 * 7 ^ 3 : ℤ_[p]) = ((231525 : ℕ) : ℤ_[p]) := by
    norm_num
  rw [heq, PadicInt.norm_natCast_eq_one_iff]
  exact ((coprime105_of_ne hp3 hp5 hp7).pow_right 3).of_dvd_right (by norm_num)

/-- The discriminant norm of `psi` is one away from `5` and `7`. -/
theorem quadraticIntegralModel_discr_norm_eq_one (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    ‖(quadraticIntegralModel (p := p)).discr‖ = 1 :=
  PadicInt.isUnit_iff.mp (quadraticIntegralModel_discr_isUnit hp5 hp7)

/-- The discriminant norm of `Psi` is one away from `3`, `5`, and `7`. -/
theorem quarticIntegralModel_discr_norm_eq_one
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    ‖(quarticIntegralModel (p := p)).discr‖ = 1 :=
  PadicInt.isUnit_iff.mp (quarticIntegralModel_discr_isUnit hp3 hp5 hp7)

/-- The normalized integral binomial model has degree `n`. -/
theorem binomialIntegralModel_natDegree (n : ℕ) (a : ℤ_[p]) :
    (binomialIntegralModel n a).natDegree = n := by
  simp [binomialIntegralModel]

/-- A positive-degree normalized integral binomial model is monic. -/
theorem binomialIntegralModel_monic {n : ℕ} (a : ℤ_[p]) (hn : 0 < n) :
    (binomialIntegralModel n a).Monic := by
  simpa only [binomialIntegralModel] using monic_X_pow_sub_C a hn.ne'

/-- The leading coefficient of a positive-degree normalized binomial model is
one. -/
theorem binomialIntegralModel_leadingCoeff {n : ℕ} (a : ℤ_[p]) (hn : 0 < n) :
    (binomialIntegralModel n a).leadingCoeff = 1 :=
  binomialIntegralModel_monic a hn

/-- The constant coefficient of a positive-degree normalized binomial model
is `-a`. -/
theorem binomialIntegralModel_coeff_zero {n : ℕ} (a : ℤ_[p]) (hn : 0 < n) :
    (binomialIntegralModel n a).coeff 0 = -a := by
  simp [binomialIntegralModel, Ne.symm hn.ne']

/-- If `a` is a unit, both endpoint coefficients of a positive-degree
normalized binomial model are units. -/
theorem binomialIntegralModel_endpoints_isUnit {n : ℕ} {a : ℤ_[p]}
    (hn : 0 < n) (ha : IsUnit a) :
    IsUnit (binomialIntegralModel n a).leadingCoeff ∧
      IsUnit ((binomialIntegralModel n a).coeff 0) := by
  rw [binomialIntegralModel_leadingCoeff a hn, binomialIntegralModel_coeff_zero a hn]
  exact ⟨isUnit_one, ha.neg⟩

/-- Under the same hypotheses, both endpoint norms of the normalized binomial
model are one. -/
theorem binomialIntegralModel_endpoint_norms {n : ℕ} {a : ℤ_[p]}
    (hn : 0 < n) (ha : IsUnit a) :
    ‖(binomialIntegralModel n a).leadingCoeff‖ = 1 ∧
      ‖(binomialIntegralModel n a).coeff 0‖ = 1 := by
  obtain ⟨hl, hc⟩ := binomialIntegralModel_endpoints_isUnit hn ha
  exact ⟨PadicInt.isUnit_iff.mp hl, PadicInt.isUnit_iff.mp hc⟩

/-- The exact discriminant of the normalized integral binomial model. -/
theorem binomialIntegralModel_discr {n : ℕ} (a : ℤ_[p]) (hn : 0 < n) :
    (binomialIntegralModel n a).discr =
      (-1 : ℤ_[p]) ^ (n * (n - 1) / 2) * (n : ℤ_[p]) ^ n *
        (-a) ^ (n - 1) := by
  simpa only [binomialIntegralModel] using discr_X_pow_sub_C hn a

/-- If `a` is a p-adic unit and `p ∤ n`, then the discriminant of
`X^n - a` is a p-adic unit. -/
theorem binomialIntegralModel_discr_isUnit {n : ℕ} {a : ℤ_[p]}
    (hn : 0 < n) (ha : IsUnit a) (hpn : ¬p ∣ n) :
    IsUnit (binomialIntegralModel n a).discr := by
  rw [binomialIntegralModel_discr a hn]
  have hnUnit : IsUnit (n : ℤ_[p]) := by
    apply natCast_isUnit_of_coprime
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpn
  exact ((isUnit_neg_one.pow (n * (n - 1) / 2)).mul
    (hnUnit.pow n)).mul (ha.neg.pow (n - 1))

/-- Under the same hypotheses, the discriminant norm of `X^n - a` is one. -/
theorem binomialIntegralModel_discr_norm_eq_one {n : ℕ} {a : ℤ_[p]}
    (hn : 0 < n) (ha : IsUnit a) (hpn : ¬p ∣ n) :
    ‖(binomialIntegralModel n a).discr‖ = 1 :=
  PadicInt.isUnit_iff.mp (binomialIntegralModel_discr_isUnit hn ha hpn)

end

end BealRegular.Signature357PadicModelUnits
