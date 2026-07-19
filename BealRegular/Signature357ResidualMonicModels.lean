import BealRegular.Signature357AdicFactorLifting

/-!
# Residual monic models for the signature `(3,5,7)` local program

This module normalizes the integral degree-seven fiber and the fixed quadratic
and quartic model factors over the p-adic integers.  Away from `3`, `5`, and
`7`, it packages the two critical reductions as coprime `MonicDegreeEq`
factorizations:

* when `u ≡ 0 (mod p)`, the residual factors have degrees `(2, 5)` and are the
  normalized quadratic model and `X^5`;
* when `u ≡ 1 (mod p)`, after translating by one, the residual factors have
  degrees `(4, 3)` and are the normalized quartic model and `X^3`.

The generic adic lifting theorem then produces exact coprime monic lifts over
`ℤ_[p]` with those prescribed reductions.  These lifts remain existential:
this module does not identify their quotient algebras with the exact
Dahmen--Siksek model algebras, prove rootwise structural stability or a Newton
polygon theorem, classify ramification, exclude signature `(3,5,7)`, or prove
Beal's conjecture.
-/

namespace BealRegular.Signature357ResidualMonicModels

open Polynomial
open scoped Ring

open Signature357BranchNormalForms
open Signature357PadicModelUnits
open Signature357AdicFactorLifting

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- The principal ideal `(p)` in the p-adic integers. -/
abbrev padicIdeal : Ideal ℤ_[p] := Ideal.span {(p : ℤ_[p])}

/-- The residue ring of the p-adic integers modulo `(p)`. -/
abbrev padicResidueRing : Type := ℤ_[p] ⧸ padicIdeal (p := p)

/-- The integral degree-seven signature `(3,5,7)` fiber. -/
def integralFiber (u : ℤ_[p]) : ℤ_[p][X] :=
  15 * X ^ 7 - 35 * X ^ 6 + 21 * X ^ 5 - C u

/-- The integral fiber scaled by the ring inverse of its leading coefficient. -/
def normalizedIntegralFiber (u : ℤ_[p]) : ℤ_[p][X] :=
  C ((15 : ℤ_[p])⁻¹ʳ) * integralFiber u

/-- The quadratic model scaled by the ring inverse of `15`. -/
def normalizedQuadraticModel : ℤ_[p][X] :=
  C ((15 : ℤ_[p])⁻¹ʳ) * quadraticIntegralModel

/-- The quartic model scaled by the ring inverse of `15`. -/
def normalizedQuarticModel : ℤ_[p][X] :=
  C ((15 : ℤ_[p])⁻¹ʳ) * quarticIntegralModel

/-- The normalized integral fiber after translating the variable by one. -/
def normalizedTranslatedIntegralFiber (u : ℤ_[p]) : ℤ_[p][X] :=
  (normalizedIntegralFiber u).comp (X + C 1)

/-- The ring inverse of `15` maps to the field inverse in the p-adic numbers
away from `3` and `5`. -/
theorem algebraMap_ringInverse_fifteen
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    algebraMap ℤ_[p] ℚ_[p] ((15 : ℤ_[p])⁻¹ʳ) = (15 : ℚ_[p])⁻¹ := by
  obtain ⟨h15, -⟩ := quadraticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h15' : IsUnit (15 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_leadingCoeff] using h15
  apply eq_inv_of_mul_eq_one_left
  change
    algebraMap ℤ_[p] ℚ_[p] ((15 : ℤ_[p])⁻¹ʳ) *
      algebraMap ℤ_[p] ℚ_[p] (15 : ℤ_[p]) = 1
  rw [← map_mul,
    Ring.inverse_mul_cancel _ h15', map_one]

/-- The normalized integral fiber maps to the normalized characteristic-zero
fiber over the p-adic numbers. -/
theorem normalizedIntegralFiber_map_padic (u : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (normalizedIntegralFiber u).map (algebraMap ℤ_[p] ℚ_[p]) =
      C (15 : ℚ_[p])⁻¹ *
        Signature357GenericLocalPolynomial.fiberK (algebraMap ℤ_[p] ℚ_[p] u) := by
  rw [normalizedIntegralFiber, Polynomial.map_mul, Polynomial.map_C,
    algebraMap_ringInverse_fifteen hp3 hp5 hp7]
  simp [integralFiber, Signature357GenericLocalPolynomial.fiberK,
    Signature357GenericLocalPolynomial.phiK]

/-- Translation by one commutes with the p-adic base change of the normalized
integral fiber. -/
theorem normalizedTranslatedIntegralFiber_map_padic (u : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (normalizedTranslatedIntegralFiber u).map (algebraMap ℤ_[p] ℚ_[p]) =
      C (15 : ℚ_[p])⁻¹ *
        (Signature357GenericLocalPolynomial.fiberK
          (algebraMap ℤ_[p] ℚ_[p] u)).comp (X + C 1) := by
  rw [normalizedTranslatedIntegralFiber, Polynomial.map_comp,
    normalizedIntegralFiber_map_padic u hp3 hp5 hp7]
  simp

theorem normalizedQuadraticModel_monic
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (normalizedQuadraticModel (p := p)).Monic := by
  obtain ⟨h15, -⟩ := quadraticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h15' : IsUnit (15 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_leadingCoeff] using h15
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [quadraticIntegralModel_leadingCoeff]
  exact Ring.inverse_mul_cancel _ h15'

theorem normalizedQuadraticModel_natDegree
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (normalizedQuadraticModel (p := p)).natDegree = 2 := by
  obtain ⟨h15, -⟩ := quadraticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h15' : IsUnit (15 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_leadingCoeff] using h15
  rw [normalizedQuadraticModel,
    natDegree_C_mul_of_isUnit h15'.ringInverse,
    quadraticIntegralModel_natDegree]

theorem normalizedQuarticModel_monic
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (normalizedQuarticModel (p := p)).Monic := by
  obtain ⟨h15, -⟩ := quarticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h15' : IsUnit (15 : ℤ_[p]) := by
    simpa only [quarticIntegralModel_leadingCoeff] using h15
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [quarticIntegralModel_leadingCoeff]
  exact Ring.inverse_mul_cancel _ h15'

theorem normalizedQuarticModel_natDegree
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (normalizedQuarticModel (p := p)).natDegree = 4 := by
  obtain ⟨h15, -⟩ := quarticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h15' : IsUnit (15 : ℤ_[p]) := by
    simpa only [quarticIntegralModel_leadingCoeff] using h15
  rw [normalizedQuarticModel,
    natDegree_C_mul_of_isUnit h15'.ringInverse,
    quarticIntegralModel_natDegree]

theorem normalizedIntegralFiber_monic (u : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (normalizedIntegralFiber u).Monic := by
  obtain ⟨h15, -⟩ := quadraticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h15' : IsUnit (15 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_leadingCoeff] using h15
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  have hdegree : (integralFiber u).natDegree = 7 := by
    simp only [integralFiber]
    compute_degree!
  rw [leadingCoeff, hdegree]
  simpa [integralFiber, coeff_X_pow] using Ring.inverse_mul_cancel (15 : ℤ_[p]) h15'

theorem normalizedIntegralFiber_natDegree (u : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (normalizedIntegralFiber u).natDegree = 7 := by
  obtain ⟨h15, -⟩ := quadraticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h15' : IsUnit (15 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_leadingCoeff] using h15
  rw [normalizedIntegralFiber,
    natDegree_C_mul_of_isUnit h15'.ringInverse]
  simp only [integralFiber]
  compute_degree!

theorem normalizedTranslatedIntegralFiber_monic (u : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (normalizedTranslatedIntegralFiber u).Monic := by
  exact (normalizedIntegralFiber_monic u hp3 hp5 hp7).comp_X_add_C 1

theorem normalizedTranslatedIntegralFiber_natDegree (u : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (normalizedTranslatedIntegralFiber u).natDegree = 7 := by
  rw [normalizedTranslatedIntegralFiber, natDegree_comp,
    normalizedIntegralFiber_natDegree u hp3 hp5 hp7]
  rw [natDegree_X_add_C]

/-- The normalized integral fiber as a monic polynomial of degree seven. -/
def normalizedIntegralFiberMonic (u : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    MonicDegreeEq ℤ_[p] 7 :=
  MonicDegreeEq.mk _ (normalizedIntegralFiber_monic u hp3 hp5 hp7)
    (normalizedIntegralFiber_natDegree u hp3 hp5 hp7)

/-- The translated normalized fiber as a monic polynomial of degree seven. -/
def normalizedTranslatedIntegralFiberMonic (u : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    MonicDegreeEq ℤ_[p] 7 :=
  MonicDegreeEq.mk _ (normalizedTranslatedIntegralFiber_monic u hp3 hp5 hp7)
    (normalizedTranslatedIntegralFiber_natDegree u hp3 hp5 hp7)

/-- The normalized quadratic model as a monic polynomial of degree two. -/
def normalizedQuadraticModelMonic
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    MonicDegreeEq ℤ_[p] 2 :=
  MonicDegreeEq.mk _ (normalizedQuadraticModel_monic hp3 hp5 hp7)
    (normalizedQuadraticModel_natDegree hp3 hp5 hp7)

/-- The normalized quartic model as a monic polynomial of degree four. -/
def normalizedQuarticModelMonic
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    MonicDegreeEq ℤ_[p] 4 :=
  MonicDegreeEq.mk _ (normalizedQuarticModel_monic hp3 hp5 hp7)
    (normalizedQuarticModel_natDegree hp3 hp5 hp7)

/-- A power of `X`, packaged as a monic polynomial of its exponent degree. -/
def xPowMonic (n : ℕ) : MonicDegreeEq ℤ_[p] n :=
  MonicDegreeEq.mk (X ^ n) (monic_X.pow n) (natDegree_X_pow n)

/-- The normalized quadratic factor reduced modulo `(p)`. -/
def zeroQuadraticResidual
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    MonicDegreeEq (padicResidueRing (p := p)) 2 :=
  (normalizedQuadraticModelMonic hp3 hp5 hp7).map
    (Ideal.Quotient.mk (padicIdeal (p := p)))

/-- The degree-five power factor reduced modulo `(p)`. -/
def zeroPowerResidual : MonicDegreeEq (padicResidueRing (p := p)) 5 :=
  (xPowMonic (p := p) 5).map (Ideal.Quotient.mk (padicIdeal (p := p)))

/-- The normalized quartic factor reduced modulo `(p)`. -/
def oneQuarticResidual
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    MonicDegreeEq (padicResidueRing (p := p)) 4 :=
  (normalizedQuarticModelMonic hp3 hp5 hp7).map
    (Ideal.Quotient.mk (padicIdeal (p := p)))

/-- The degree-three power factor reduced modulo `(p)`. -/
def onePowerResidual : MonicDegreeEq (padicResidueRing (p := p)) 3 :=
  (xPowMonic (p := p) 3).map (Ideal.Quotient.mk (padicIdeal (p := p)))

theorem normalizedIntegralFiber_zero_factorization :
    normalizedIntegralFiber (p := p) 0 =
      normalizedQuadraticModel (p := p) * X ^ 5 := by
  simp [normalizedIntegralFiber, integralFiber, normalizedQuadraticModel,
    quadraticIntegralModel, psiK]
  ring

theorem normalizedTranslatedIntegralFiber_one_factorization :
    normalizedTranslatedIntegralFiber (p := p) 1 =
      normalizedQuarticModel (p := p) * X ^ 3 := by
  simp [normalizedTranslatedIntegralFiber, normalizedIntegralFiber, integralFiber,
    normalizedQuarticModel, quarticIntegralModel, PsiK]
  ring

theorem zeroBranch_residual_factorization
    (u : ℤ_[p]) (hu : u ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (zeroQuadraticResidual hp3 hp5 hp7).1 * zeroPowerResidual.1 =
      (normalizedIntegralFiberMonic u hp3 hp5 hp7).1.map
        (Ideal.Quotient.mk (padicIdeal (p := p))) := by
  change
    (normalizedQuadraticModel (p := p)).map
        (Ideal.Quotient.mk (padicIdeal (p := p))) *
      ((X : ℤ_[p][X]) ^ 5).map
        (Ideal.Quotient.mk (padicIdeal (p := p))) =
    (normalizedIntegralFiber u).map
      (Ideal.Quotient.mk (padicIdeal (p := p)))
  have hu0 : Ideal.Quotient.mk (padicIdeal (p := p)) u = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hu
  rw [show (normalizedIntegralFiber u).map
      (Ideal.Quotient.mk (padicIdeal (p := p))) =
      (normalizedIntegralFiber 0).map
        (Ideal.Quotient.mk (padicIdeal (p := p))) by
    simp [normalizedIntegralFiber, integralFiber, hu0]]
  rw [normalizedIntegralFiber_zero_factorization,
    Polynomial.map_mul]

theorem oneBranch_residual_factorization
    (u : ℤ_[p]) (hu : u - 1 ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (oneQuarticResidual hp3 hp5 hp7).1 * onePowerResidual.1 =
      (normalizedTranslatedIntegralFiberMonic u hp3 hp5 hp7).1.map
        (Ideal.Quotient.mk (padicIdeal (p := p))) := by
  change
    (normalizedQuarticModel (p := p)).map
        (Ideal.Quotient.mk (padicIdeal (p := p))) *
      ((X : ℤ_[p][X]) ^ 3).map
        (Ideal.Quotient.mk (padicIdeal (p := p))) =
    (normalizedTranslatedIntegralFiber u).map
      (Ideal.Quotient.mk (padicIdeal (p := p)))
  have hu1 : Ideal.Quotient.mk (padicIdeal (p := p)) u = 1 := by
    rw [← sub_eq_zero]
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hu)
  rw [show (normalizedTranslatedIntegralFiber u).map
      (Ideal.Quotient.mk (padicIdeal (p := p))) =
      (normalizedTranslatedIntegralFiber 1).map
        (Ideal.Quotient.mk (padicIdeal (p := p))) by
    simp [normalizedTranslatedIntegralFiber, normalizedIntegralFiber,
      integralFiber, hu1]]
  rw [normalizedTranslatedIntegralFiber_one_factorization,
    Polynomial.map_mul]

theorem zeroBranch_residual_isCoprime
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    IsCoprime (zeroQuadraticResidual hp3 hp5 hp7).1 zeroPowerResidual.1 := by
  rw [show (zeroPowerResidual (p := p)).1 =
      (X : (padicResidueRing (p := p))[X]) ^ 5 by
    simp [zeroPowerResidual, xPowMonic, MonicDegreeEq.map]]
  apply isCoprime_X_pow_of_coeff_zero_isUnit
  obtain ⟨h15, h21⟩ := quadraticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h15' : IsUnit (15 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_leadingCoeff] using h15
  have h21' : IsUnit (21 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_coeff_zero] using h21
  have hcoeff : IsUnit ((normalizedQuadraticModel (p := p)).coeff 0) := by
    rw [normalizedQuadraticModel, coeff_C_mul,
      quadraticIntegralModel_coeff_zero]
    exact h15'.ringInverse.mul h21'
  change IsUnit
    (((normalizedQuadraticModelMonic hp3 hp5 hp7).map
      (Ideal.Quotient.mk (padicIdeal (p := p)))).1.coeff 0)
  rw [MonicDegreeEq.map_coe, coeff_map,
    show (normalizedQuadraticModelMonic hp3 hp5 hp7).1 =
      normalizedQuadraticModel (p := p) by rfl]
  exact hcoeff.map (Ideal.Quotient.mk (padicIdeal (p := p)))

theorem oneBranch_residual_isCoprime
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    IsCoprime (oneQuarticResidual hp3 hp5 hp7).1 onePowerResidual.1 := by
  rw [show (onePowerResidual (p := p)).1 =
      (X : (padicResidueRing (p := p))[X]) ^ 3 by
    simp [onePowerResidual, xPowMonic, MonicDegreeEq.map]]
  apply isCoprime_X_pow_of_coeff_zero_isUnit
  obtain ⟨h15, h35⟩ := quarticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h15' : IsUnit (15 : ℤ_[p]) := by
    simpa only [quarticIntegralModel_leadingCoeff] using h15
  have h35' : IsUnit (35 : ℤ_[p]) := by
    simpa only [quarticIntegralModel_coeff_zero] using h35
  have hcoeff : IsUnit ((normalizedQuarticModel (p := p)).coeff 0) := by
    rw [normalizedQuarticModel, coeff_C_mul,
      quarticIntegralModel_coeff_zero]
    exact h15'.ringInverse.mul h35'
  change IsUnit
    (((normalizedQuarticModelMonic hp3 hp5 hp7).map
      (Ideal.Quotient.mk (padicIdeal (p := p)))).1.coeff 0)
  rw [MonicDegreeEq.map_coe, coeff_map,
    show (normalizedQuarticModelMonic hp3 hp5 hp7).1 =
      normalizedQuarticModel (p := p) by rfl]
  exact hcoeff.map (Ideal.Quotient.mk (padicIdeal (p := p)))

theorem zeroBranch_residual_liftingData
    (u : ℤ_[p]) (hu : u ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (zeroQuadraticResidual hp3 hp5 hp7).1 * zeroPowerResidual.1 =
        (normalizedIntegralFiberMonic u hp3 hp5 hp7).1.map
          (Ideal.Quotient.mk (padicIdeal (p := p))) ∧
      IsCoprime (zeroQuadraticResidual hp3 hp5 hp7).1 zeroPowerResidual.1 :=
  ⟨zeroBranch_residual_factorization u hu hp3 hp5 hp7,
    zeroBranch_residual_isCoprime hp3 hp5 hp7⟩

theorem oneBranch_residual_liftingData
    (u : ℤ_[p]) (hu : u - 1 ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (oneQuarticResidual hp3 hp5 hp7).1 * onePowerResidual.1 =
        (normalizedTranslatedIntegralFiberMonic u hp3 hp5 hp7).1.map
          (Ideal.Quotient.mk (padicIdeal (p := p))) ∧
      IsCoprime (oneQuarticResidual hp3 hp5 hp7).1 onePowerResidual.1 :=
  ⟨oneBranch_residual_factorization u hu hp3 hp5 hp7,
    oneBranch_residual_isCoprime hp3 hp5 hp7⟩

theorem zeroBranch_exists_coprime_monic_factorization
    (u : ℤ_[p]) (hu : u ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    ∃ (f : MonicDegreeEq ℤ_[p] 2) (g : MonicDegreeEq ℤ_[p] 5),
      f.1 * g.1 = (normalizedIntegralFiberMonic u hp3 hp5 hp7).1 ∧
        IsCoprime f.1 g.1 ∧
        f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
          zeroQuadraticResidual hp3 hp5 hp7 ∧
        g.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
          zeroPowerResidual := by
  letI : IsAdicComplete (padicIdeal (p := p)) ℤ_[p] :=
    padicInt_span_p_isAdicComplete
  obtain ⟨hfac, hcoprime⟩ := zeroBranch_residual_liftingData u hu hp3 hp5 hp7
  exact exists_coprime_monic_factorization_of_isAdicComplete
    (padicIdeal (p := p)) (by norm_num) _ _ _ hfac hcoprime

theorem oneBranch_exists_coprime_monic_factorization
    (u : ℤ_[p]) (hu : u - 1 ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    ∃ (f : MonicDegreeEq ℤ_[p] 4) (g : MonicDegreeEq ℤ_[p] 3),
      f.1 * g.1 = (normalizedTranslatedIntegralFiberMonic u hp3 hp5 hp7).1 ∧
        IsCoprime f.1 g.1 ∧
        f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
          oneQuarticResidual hp3 hp5 hp7 ∧
        g.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
          onePowerResidual := by
  letI : IsAdicComplete (padicIdeal (p := p)) ℤ_[p] :=
    padicInt_span_p_isAdicComplete
  obtain ⟨hfac, hcoprime⟩ := oneBranch_residual_liftingData u hu hp3 hp5 hp7
  exact exists_coprime_monic_factorization_of_isAdicComplete
    (padicIdeal (p := p)) (by norm_num) _ _ _ hfac hcoprime

/-- When `u ≡ 0 (mod p)`, the normalized p-adic fiber has coprime monic
factors of degrees two and five with the prescribed residual models, and its
quotient algebra over `ℚ_[p]` decomposes as their product. -/
theorem zeroBranch_exists_factorization_and_padicDecomposition
    (u : ℤ_[p]) (hu : u ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    ∃ (f : MonicDegreeEq ℤ_[p] 2) (g : MonicDegreeEq ℤ_[p] 5),
      f.1 * g.1 = (normalizedIntegralFiberMonic u hp3 hp5 hp7).1 ∧
        IsCoprime f.1 g.1 ∧
        f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
          zeroQuadraticResidual hp3 hp5 hp7 ∧
        g.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
          zeroPowerResidual ∧
        Nonempty
          (AdjoinRoot
              (C (15 : ℚ_[p])⁻¹ *
                Signature357GenericLocalPolynomial.fiberK
                  (algebraMap ℤ_[p] ℚ_[p] u)) ≃ₐ[ℚ_[p]]
            AdjoinRoot (f.1.map (algebraMap ℤ_[p] ℚ_[p])) ×
              AdjoinRoot (g.1.map (algebraMap ℤ_[p] ℚ_[p]))) := by
  letI : IsAdicComplete (padicIdeal (p := p)) ℤ_[p] :=
    padicInt_span_p_isAdicComplete
  obtain ⟨hfac, hcoprime⟩ := zeroBranch_residual_liftingData u hu hp3 hp5 hp7
  obtain ⟨f, g, hfg, hcop, hf0, hg0, hdecomp⟩ :=
    exists_factorization_and_fieldBaseChangeDecomposition
      (R := ℤ_[p]) (K := ℚ_[p]) (padicIdeal (p := p)) (by norm_num)
      (normalizedIntegralFiberMonic u hp3 hp5 hp7)
      (zeroQuadraticResidual hp3 hp5 hp7) zeroPowerResidual hfac hcoprime
  refine ⟨f, g, hfg, hcop, hf0, hg0, ?_⟩
  have hmap :
      (normalizedIntegralFiberMonic u hp3 hp5 hp7).1.map
          (algebraMap ℤ_[p] ℚ_[p]) =
        C (15 : ℚ_[p])⁻¹ *
          Signature357GenericLocalPolynomial.fiberK
            (algebraMap ℤ_[p] ℚ_[p] u) := by
    change (normalizedIntegralFiber u).map (algebraMap ℤ_[p] ℚ_[p]) = _
    exact normalizedIntegralFiber_map_padic u hp3 hp5 hp7
  rw [hmap] at hdecomp
  exact hdecomp

/-- When `u ≡ 1 (mod p)`, the translated normalized p-adic fiber has coprime
monic factors of degrees four and three with the prescribed residual models,
and its quotient algebra over `ℚ_[p]` decomposes as their product. -/
theorem oneBranch_exists_factorization_and_padicDecomposition
    (u : ℤ_[p]) (hu : u - 1 ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    ∃ (f : MonicDegreeEq ℤ_[p] 4) (g : MonicDegreeEq ℤ_[p] 3),
      f.1 * g.1 = (normalizedTranslatedIntegralFiberMonic u hp3 hp5 hp7).1 ∧
        IsCoprime f.1 g.1 ∧
        f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
          oneQuarticResidual hp3 hp5 hp7 ∧
        g.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
          onePowerResidual ∧
        Nonempty
          (AdjoinRoot
              (C (15 : ℚ_[p])⁻¹ *
                (Signature357GenericLocalPolynomial.fiberK
                  (algebraMap ℤ_[p] ℚ_[p] u)).comp (X + C 1)) ≃ₐ[ℚ_[p]]
            AdjoinRoot (f.1.map (algebraMap ℤ_[p] ℚ_[p])) ×
              AdjoinRoot (g.1.map (algebraMap ℤ_[p] ℚ_[p]))) := by
  letI : IsAdicComplete (padicIdeal (p := p)) ℤ_[p] :=
    padicInt_span_p_isAdicComplete
  obtain ⟨hfac, hcoprime⟩ := oneBranch_residual_liftingData u hu hp3 hp5 hp7
  obtain ⟨f, g, hfg, hcop, hf0, hg0, hdecomp⟩ :=
    exists_factorization_and_fieldBaseChangeDecomposition
      (R := ℤ_[p]) (K := ℚ_[p]) (padicIdeal (p := p)) (by norm_num)
      (normalizedTranslatedIntegralFiberMonic u hp3 hp5 hp7)
      (oneQuarticResidual hp3 hp5 hp7) onePowerResidual hfac hcoprime
  refine ⟨f, g, hfg, hcop, hf0, hg0, ?_⟩
  have hmap :
      (normalizedTranslatedIntegralFiberMonic u hp3 hp5 hp7).1.map
          (algebraMap ℤ_[p] ℚ_[p]) =
        C (15 : ℚ_[p])⁻¹ *
          (Signature357GenericLocalPolynomial.fiberK
            (algebraMap ℤ_[p] ℚ_[p] u)).comp (X + C 1) := by
    change (normalizedTranslatedIntegralFiber u).map
      (algebraMap ℤ_[p] ℚ_[p]) = _
    exact normalizedTranslatedIntegralFiber_map_padic u hp3 hp5 hp7
  rw [hmap] at hdecomp
  exact hdecomp

end

end BealRegular.Signature357ResidualMonicModels
