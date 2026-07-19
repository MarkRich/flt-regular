import BealRegular.Signature357BranchNormalForms
import BealRegular.Signature357SmallBinomialRigidity

/-!
# The septic model on the signature `(3,5,7)` infinity branch

Let `p` be different from `3`, `5`, and `7`, let `q` be a nonzero element of
the maximal ideal of `ℤ_[p]`, and let `a` be a unit.  This module identifies
the whole degree-seven p-adic fiber at `q⁻⁷ a` with the binomial model
`X ^ 7 - 15⁻¹ a`.

The proof first normalizes the inverse-scaled polynomial from the paper.  Its
terms of degrees six and five vanish modulo `p`, leaving a separable septic
binomial.  Complete-adic formal-etale rigidity identifies the normalized
integral algebra with that binomial model, and root scaling returns to the
original fiber.

This is an equivalence of finite p-adic algebras.  It does not say that the
binomial is irreducible or that either algebra is a field, classify
ramification, exclude signature `(3,5,7)`, or prove Beal's conjecture.
-/

namespace BealRegular.Signature357SevenBranchCompletion

open Polynomial
open scoped Ring

open Signature357GenericLocalPolynomial
open Signature357ModelFactorAlgebras
open Signature357PadicModelUnits
open Signature357ResidualMonicModels
open Signature357SmallBinomialRigidity
open WeightedPolynomialScaling

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- The monic integral polynomial obtained from the infinity branch after
inverse scaling and normalization by `15`. -/
def sevenBranchIntegralModel (q a : ℤ_[p]) : ℤ_[p][X] :=
  X ^ 7 +
    (-C ((15 : ℤ_[p])⁻¹ʳ * (35 * q)) * X ^ 6 +
      C ((15 : ℤ_[p])⁻¹ʳ * (21 * q ^ 2)) * X ^ 5 -
        C ((15 : ℤ_[p])⁻¹ʳ * a))

/-- The normalized infinity-branch model is monic. -/
theorem sevenBranchIntegralModel_monic (q a : ℤ_[p]) :
    (sevenBranchIntegralModel q a).Monic := by
  rw [sevenBranchIntegralModel]
  apply monic_X_pow_add
  compute_degree!

/-- The normalized infinity-branch model has degree seven. -/
theorem sevenBranchIntegralModel_natDegree (q a : ℤ_[p]) :
    (sevenBranchIntegralModel q a).natDegree = 7 := by
  rw [sevenBranchIntegralModel]
  compute_degree!

/-- The normalized infinity-branch model packaged with its monicity and
degree. -/
def sevenBranchIntegralModelMonic (q a : ℤ_[p]) :
    MonicDegreeEq ℤ_[p] 7 :=
  MonicDegreeEq.mk _ (sevenBranchIntegralModel_monic q a)
    (sevenBranchIntegralModel_natDegree q a)

/-- Modulo the maximal ideal, the normalized infinity-branch model is exactly
`X ^ 7 - 15⁻¹ a`. -/
theorem sevenBranchIntegralModel_reduction
    (q a : ℤ_[p]) (hqI : q ∈ padicIdeal (p := p)) :
    (sevenBranchIntegralModel q a).map
        (Ideal.Quotient.mk (padicIdeal (p := p))) =
      (binomialIntegralModel 7 ((15 : ℤ_[p])⁻¹ʳ * a)).map
        (Ideal.Quotient.mk (padicIdeal (p := p))) := by
  let π : ℤ_[p] →+* padicResidueRing (p := p) :=
    Ideal.Quotient.mk (padicIdeal (p := p))
  have hq0 : π q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hqI
  simp [sevenBranchIntegralModel, binomialIntegralModel, π, hq0]
  ring

private theorem scaleRoots_eq_C_pow_mul_comp_inv
    {K : Type*} [Field K] (P : K[X]) (q : K) (hq : q ≠ 0) :
    P.scaleRoots q =
      C (q ^ P.natDegree) * P.comp (C q⁻¹ * X) := by
  ext i
  rw [coeff_scaleRoots, coeff_C_mul, comp_C_mul_X_coeff]
  by_cases hi : i ≤ P.natDegree
  · calc
      P.coeff i * q ^ (P.natDegree - i) =
          P.coeff i * q ^ (P.natDegree - i) *
            (q ^ i * (q⁻¹) ^ i) := by
              rw [← mul_pow, mul_inv_cancel₀ hq, one_pow, mul_one]
      _ = (q ^ (P.natDegree - i) * q ^ i) *
            (P.coeff i * q⁻¹ ^ i) := by ring
      _ = q ^ P.natDegree * (P.coeff i * q⁻¹ ^ i) := by
            rw [← pow_add, Nat.sub_add_cancel hi]
  · have hcoeff : P.coeff i = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hi)
    simp [hcoeff]

/-- Scaling the roots of the normalized original fiber by `q` gives the
base change of the normalized integral infinity-branch model. -/
theorem normalizedFiber_scaleRoots_eq_model_map
    (q a : ℤ_[p]) (hq : q ≠ 0)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (C (15 : ℚ_[p])⁻¹ *
        fiberK ((algebraMap ℤ_[p] ℚ_[p] q)⁻¹ ^ 7 *
          algebraMap ℤ_[p] ℚ_[p] a)).scaleRoots
          (algebraMap ℤ_[p] ℚ_[p] q) =
      (sevenBranchIntegralModel q a).map
        (algebraMap ℤ_[p] ℚ_[p]) := by
  have hdeg :
      (C (15 : ℚ_[p])⁻¹ *
          fiberK ((algebraMap ℤ_[p] ℚ_[p] q)⁻¹ ^ 7 *
            algebraMap ℤ_[p] ℚ_[p] a)).natDegree = 7 := by
    rw [natDegree_C_mul (inv_ne_zero (by norm_num)), fiberK_natDegree]
  let qQ : ℚ_[p] := algebraMap ℤ_[p] ℚ_[p] q
  let aQ : ℚ_[p] := algebraMap ℤ_[p] ℚ_[p] a
  have hqQ : qQ ≠ 0 :=
    (IsFractionRing.injective ℤ_[p] ℚ_[p]).ne hq
  have hbranch :=
    Signature357BranchNormalForms.sevenBranch_scaled_normalForm
      qQ aQ hqQ
  have hmodelMap :
      (sevenBranchIntegralModel q a).map
          (algebraMap ℤ_[p] ℚ_[p]) =
        C (15 : ℚ_[p])⁻¹ *
          (15 * X ^ 7 - C (35 * qQ) * X ^ 6 +
            C (21 * qQ ^ 2) * X ^ 5 - C aQ) := by
    rw [sevenBranchIntegralModel]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_neg,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, map_mul, map_pow, map_ofNat]
    rw [algebraMap_ringInverse_fifteen hp3 hp5 hp7]
    simp only [qQ, aQ]
    norm_num
    have hscalar :
        (C (1 / 15 : ℚ_[p]) : ℚ_[p][X]) * 15 = 1 := by
      rw [show (15 : ℚ_[p][X]) = C (15 : ℚ_[p]) by rw [C_ofNat]]
      rw [← C_mul]
      norm_num
    nth_rewrite 1 [← one_mul ((X : ℚ_[p][X]) ^ 7)]
    nth_rewrite 1 [← hscalar]
    ring
  rw [scaleRoots_eq_C_pow_mul_comp_inv _ qQ hqQ, hdeg]
  simp only [mul_comp, C_comp]
  rw [show (algebraMap ℤ_[p] ℚ_[p] q) = qQ by rfl]
  rw [show (algebraMap ℤ_[p] ℚ_[p] a) = aQ by rfl]
  rw [show C (qQ ^ 7) *
      (C (15 : ℚ_[p])⁻¹ *
        (fiberK (qQ⁻¹ ^ 7 * aQ)).comp (C qQ⁻¹ * X)) =
      C (15 : ℚ_[p])⁻¹ *
        (C (qQ ^ 7) *
          (fiberK (qQ⁻¹ ^ 7 * aQ)).comp (C qQ⁻¹ * X)) by ring]
  rw [hbranch, ← hmodelMap]

private theorem fiber_associated_normalized (P : ℚ_[p][X]) :
    Associated P (C (15 : ℚ_[p])⁻¹ * P) := by
  have hunit : IsUnit (C (15 : ℚ_[p])⁻¹ : ℚ_[p][X]) := by
    rw [isUnit_C, isUnit_iff_ne_zero]
    exact inv_ne_zero (by norm_num)
  exact (associated_unit_mul_left P (C (15 : ℚ_[p])⁻¹) hunit).symm

private def adjoinRootNormalizationEquiv (P : ℚ_[p][X]) :
    AdjoinRoot P ≃ₐ[ℚ_[p]] AdjoinRoot (C (15 : ℚ_[p])⁻¹ * P) :=
  AdjoinRoot.algEquivOfAssociated ℚ_[p] P
    (C (15 : ℚ_[p])⁻¹ * P) (fiber_associated_normalized P)

/-- The original p-adic infinity-branch fiber is the septic binomial model
with parameter `15⁻¹ a`.  No irreducibility or field claim is made. -/
def sevenBranchFixedModelPadicEquiv
    (q a : ℤ_[p]) (ha : IsUnit a) (hq : q ≠ 0)
    (hqI : q ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    AdjoinRoot
        (fiberK ((algebraMap ℤ_[p] ℚ_[p] q)⁻¹ ^ 7 *
          algebraMap ℤ_[p] ℚ_[p] a)) ≃ₐ[ℚ_[p]]
      BinomialModelAlgebra 7
        (algebraMap ℤ_[p] ℚ_[p] ((15 : ℤ_[p])⁻¹ʳ * a)) := by
  let qQ : ℚ_[p] := algebraMap ℤ_[p] ℚ_[p] q
  let u : ℚ_[p] := qQ⁻¹ ^ 7 * algebraMap ℤ_[p] ℚ_[p] a
  let N : ℚ_[p][X] := C (15 : ℚ_[p])⁻¹ * fiberK u
  have hqQ : qQ ≠ 0 :=
    (IsFractionRing.injective ℤ_[p] ℚ_[p]).ne hq
  have hqUnit : IsUnit qQ := isUnit_iff_ne_zero.mpr hqQ
  obtain ⟨h15, -⟩ :=
    quadraticIntegralModel_endpoints_isUnit (p := p) hp3 hp5 hp7
  have h15' : IsUnit (15 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_leadingCoeff] using h15
  have hb : IsUnit ((15 : ℤ_[p])⁻¹ʳ * a) :=
    h15'.ringInverse.mul ha
  have hpn : ¬p ∣ 7 := by
    intro hpdiv
    exact hp7 ((Nat.prime_dvd_prime_iff_eq
      (Fact.out : p.Prime) Nat.prime_seven).mp hpdiv)
  have hred := sevenBranchIntegralModel_reduction
    (p := p) q a hqI
  have hscale := normalizedFiber_scaleRoots_eq_model_map
    (p := p) q a hq hp3 hp5 hp7
  change AdjoinRoot (fiberK u) ≃ₐ[ℚ_[p]]
    BinomialModelAlgebra 7
      (algebraMap ℤ_[p] ℚ_[p] ((15 : ℤ_[p])⁻¹ʳ * a))
  exact (adjoinRootNormalizationEquiv (fiberK u)).trans <|
    (adjoinRootScaleRootsAlgEquiv N qQ hqUnit).symm.trans <|
      (AdjoinRoot.algEquivOfEq ℚ_[p] _ _ hscale).trans <|
        descaledSmallFactorPadicAlgEquiv
          (sevenBranchIntegralModelMonic q a)
          ((15 : ℤ_[p])⁻¹ʳ * a) hb hpn hred

end

end BealRegular.Signature357SevenBranchCompletion
