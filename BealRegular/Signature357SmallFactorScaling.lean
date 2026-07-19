import BealRegular.Signature357ResidualMonicModels
import BealRegular.WeightedPolynomialScaling

/-!
# Integral scaling of the small signature `(3,5,7)` factors

This module specializes weighted polynomial root scaling to the two critical
fibers in the signature `(3,5,7)` local program.  A lift of the fixed
quadratic or quartic residual factor has unit constant coefficient.  The
normalized fiber has the complementary ideal-power bounds needed to transfer
weighted divisibility to the degree-five or degree-three factor, respectively.
Consequently those small factors have integral descales through
`Polynomial.scaleRoots`.

The descaled polynomials remain existential here.  This module does not
identify their reductions with binomials, construct quotient-algebra
equivalences, classify ramification, exclude signature `(3,5,7)`, or prove
Beal's conjecture.
-/

namespace BealRegular.Signature357SmallFactorScaling

open Polynomial
open scoped Ring

open Signature357PadicModelUnits
open Signature357ResidualMonicModels
open WeightedPolynomialScaling

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- The constant coefficient of a degree-two lift of the zero-branch model is
a p-adic unit. -/
theorem zeroLargeFactor_coeff_zero_isUnit
    (f : MonicDegreeEq ℤ_[p] 2)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (hred : f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      zeroQuadraticResidual hp3 hp5 hp7) :
    IsUnit (f.1.coeff 0) := by
  obtain ⟨h15, h21⟩ :=
    quadraticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h15' : IsUnit (15 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_leadingCoeff] using h15
  have h21' : IsUnit (21 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_coeff_zero] using h21
  have hmodel : IsUnit ((normalizedQuadraticModel (p := p)).coeff 0) := by
    rw [normalizedQuadraticModel, coeff_C_mul,
      quadraticIntegralModel_coeff_zero]
    exact h15'.ringInverse.mul h21'
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  have hredpoly := congrArg Subtype.val hred
  change f.1.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
    (normalizedQuadraticModel (p := p)).map
      (Ideal.Quotient.mk (padicIdeal (p := p))) at hredpoly
  have hredres : f.1.map (IsLocalRing.residue ℤ_[p]) =
      (normalizedQuadraticModel (p := p)).map
        (IsLocalRing.residue ℤ_[p]) := by
    change f.1.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p])) =
      (normalizedQuadraticModel (p := p)).map
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p]))
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact hredpoly
  have hcoeff := congrArg
    (fun P : (IsLocalRing.ResidueField ℤ_[p])[X] ↦ P.coeff 0) hredres
  simp only [coeff_map] at hcoeff
  rw [hcoeff]
  exact (hmodel.map (IsLocalRing.residue ℤ_[p])).ne_zero

/-- The constant coefficient of a degree-four lift of the translated-one
model is a p-adic unit. -/
theorem oneLargeFactor_coeff_zero_isUnit
    (f : MonicDegreeEq ℤ_[p] 4)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (hred : f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      oneQuarticResidual hp3 hp5 hp7) :
    IsUnit (f.1.coeff 0) := by
  obtain ⟨h15, h35⟩ :=
    quarticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h15' : IsUnit (15 : ℤ_[p]) := by
    simpa only [quarticIntegralModel_leadingCoeff] using h15
  have h35' : IsUnit (35 : ℤ_[p]) := by
    simpa only [quarticIntegralModel_coeff_zero] using h35
  have hmodel : IsUnit ((normalizedQuarticModel (p := p)).coeff 0) := by
    rw [normalizedQuarticModel, coeff_C_mul,
      quarticIntegralModel_coeff_zero]
    exact h15'.ringInverse.mul h35'
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  have hredpoly := congrArg Subtype.val hred
  change f.1.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
    (normalizedQuarticModel (p := p)).map
      (Ideal.Quotient.mk (padicIdeal (p := p))) at hredpoly
  have hredres : f.1.map (IsLocalRing.residue ℤ_[p]) =
      (normalizedQuarticModel (p := p)).map
        (IsLocalRing.residue ℤ_[p]) := by
    change f.1.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p])) =
      (normalizedQuarticModel (p := p)).map
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p]))
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact hredpoly
  have hcoeff := congrArg
    (fun P : (IsLocalRing.ResidueField ℤ_[p])[X] ↦ P.coeff 0) hredres
  simp only [coeff_map] at hcoeff
  rw [hcoeff]
  exact (hmodel.map (IsLocalRing.residue ℤ_[p])).ne_zero

/-- The normalized zero-branch fiber has the weighted low-coefficient bounds
needed to descale its degree-five factor by `q`. -/
theorem zeroFiber_weightedCoeffs
    (q a : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    ∀ i < 5,
      (normalizedIntegralFiberMonic (q ^ 5 * a) hp3 hp5 hp7).1.coeff i ∈
        (Ideal.span {q}) ^ (5 - i) := by
  intro i hi
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  change q ^ (5 - i) ∣
    (C ((15 : ℤ_[p])⁻¹ʳ) *
      (15 * X ^ 7 - 35 * X ^ 6 + 21 * X ^ 5 - C (q ^ 5 * a))).coeff i
  rw [coeff_C_mul]
  interval_cases i
  · refine ⟨-((15 : ℤ_[p])⁻¹ʳ * a), ?_⟩
    rw [coeff_sub, coeff_C]
    simp [coeff_X_pow]
    ring
  all_goals
    rw [coeff_sub, coeff_C]
    simp [coeff_X_pow]

private theorem translatedFiber_normalForm (q a : ℤ_[p]) :
    normalizedTranslatedIntegralFiber (p := p) (1 + q ^ 3 * a) =
      C ((15 : ℤ_[p])⁻¹ʳ) *
        (X ^ 3 * quarticIntegralModel - C (q ^ 3 * a)) := by
  simp [normalizedTranslatedIntegralFiber, normalizedIntegralFiber,
    integralFiber, quarticIntegralModel,
    Signature357BranchNormalForms.PsiK]
  ring_nf
  simp

/-- The normalized translated-one fiber has the weighted low-coefficient
bounds needed to descale its degree-three factor by `q`. -/
theorem oneTranslatedFiber_weightedCoeffs
    (q a : ℤ_[p]) :
    ∀ i < 3,
      (normalizedTranslatedIntegralFiber (p := p) (1 + q ^ 3 * a)).coeff i ∈
        (Ideal.span {q}) ^ (3 - i) := by
  have hc0 : ((C q : ℤ_[p][X]) ^ 3).coeff 0 = q ^ 3 := by
    rw [← C_pow, coeff_C]
    simp
  have hc1 : ((C q : ℤ_[p][X]) ^ 3).coeff 1 = 0 := by
    rw [← C_pow, coeff_C]
    simp
  have hc2 : ((C q : ℤ_[p][X]) ^ 3).coeff 2 = 0 := by
    rw [← C_pow, coeff_C]
    simp
  intro i hi
  interval_cases i
  · rw [translatedFiber_normalForm, coeff_C_mul, coeff_sub,
      coeff_X_pow_mul']
    norm_num [hc0]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨(15 : ℤ_[p])⁻¹ʳ * a, by ring⟩
  · rw [translatedFiber_normalForm, coeff_C_mul, coeff_sub,
      coeff_X_pow_mul']
    norm_num [hc1]
  · rw [translatedFiber_normalForm, coeff_C_mul, coeff_sub,
      coeff_X_pow_mul']
    norm_num [hc2]

/-- A degree-five factor in the zero branch admits an integral monic descale
through the change of roots by `q`. -/
theorem exists_zeroBranch_descaled_quintic
    (q a : ℤ_[p])
    (f : MonicDegreeEq ℤ_[p] 2) (g : MonicDegreeEq ℤ_[p] 5)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (hfac : f.1 * g.1 =
      (normalizedIntegralFiberMonic (q ^ 5 * a) hp3 hp5 hp7).1)
    (hlarge : f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      zeroQuadraticResidual hp3 hp5 hp7) :
    ∃ G : MonicDegreeEq ℤ_[p] 5, G.1.scaleRoots q = g.1 := by
  have hf0 : IsUnit (f.1.coeff 0) :=
    zeroLargeFactor_coeff_zero_isUnit f hp3 hp5 hp7 hlarge
  have hgweighted : ∀ i < 5,
      g.1.coeff i ∈ (Ideal.span {q}) ^ (5 - i) :=
    weightedCoeff_mem_of_mul_eq_of_constantCoeff_isUnit
      (Ideal.span {q})
      (normalizedIntegralFiber (p := p) (q ^ 5 * a))
      f.1 g.1 hfac.symm hf0
      (zeroFiber_weightedCoeffs q a hp3 hp5 hp7)
  exact exists_monicDegreeEq_scaleRoots_eq_of_mem_span_pow g q hgweighted

/-- A degree-three factor in the translated-one branch admits an integral
monic descale through the change of roots by `q`. -/
theorem exists_oneBranch_descaled_cubic
    (q a : ℤ_[p])
    (f : MonicDegreeEq ℤ_[p] 4) (g : MonicDegreeEq ℤ_[p] 3)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (hfac : f.1 * g.1 =
      (normalizedTranslatedIntegralFiberMonic
        (1 + q ^ 3 * a) hp3 hp5 hp7).1)
    (hlarge : f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      oneQuarticResidual hp3 hp5 hp7) :
    ∃ G : MonicDegreeEq ℤ_[p] 3, G.1.scaleRoots q = g.1 := by
  have hf0 : IsUnit (f.1.coeff 0) :=
    oneLargeFactor_coeff_zero_isUnit f hp3 hp5 hp7 hlarge
  have hgweighted : ∀ i < 3,
      g.1.coeff i ∈ (Ideal.span {q}) ^ (3 - i) :=
    weightedCoeff_mem_of_mul_eq_of_constantCoeff_isUnit
      (Ideal.span {q})
      (normalizedTranslatedIntegralFiber (p := p) (1 + q ^ 3 * a))
      f.1 g.1 hfac.symm hf0
      (oneTranslatedFiber_weightedCoeffs q a)
  exact exists_monicDegreeEq_scaleRoots_eq_of_mem_span_pow g q hgweighted

end

end BealRegular.Signature357SmallFactorScaling
