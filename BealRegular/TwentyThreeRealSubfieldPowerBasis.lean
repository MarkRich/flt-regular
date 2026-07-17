module

public import BealRegular.TwentyThreeRealSubfieldEisenstein
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# A rational power basis for the real subfield at 23

The explicit element `alpha = -(zeta_23 + zeta_23⁻¹)` is integral over `ℚ`
and generates the maximal real subfield.  These facts package its powers into
a `PowerBasis ℚ K23plus`, ready for discriminant calculations.
-/

@[expose] public section

namespace BealRegular.TwentyThreeRealSubfieldPowerBasis

open BealRegular.TwentyThreeRealSubfield
open BealRegular.TwentyThreeRealSubfieldEisenstein
open Polynomial

noncomputable section

local notation "K23" => CyclotomicField 23 ℚ
local notation "K23plus" => NumberField.maximalRealSubfield K23

theorem alpha_isIntegral_rat : IsIntegral ℚ alpha :=
  ⟨realSubfieldPolynomialRat, realSubfieldPolynomialRat_monic,
    aeval_realSubfieldPolynomialRat_alpha⟩

theorem alpha_isIntegral_int : IsIntegral ℤ alpha :=
  ⟨realSubfieldPolynomial, realSubfieldPolynomial_monic,
    aeval_realSubfieldPolynomial_alpha⟩

theorem realSubfieldPolynomial_eq_minpoly_int_alpha :
    realSubfieldPolynomial = minpoly ℤ alpha := by
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have hcast : algebraMap ℤ ℚ = Int.castRingHom ℚ :=
    RingHom.ext_int _ _
  calc
    realSubfieldPolynomial.map (Int.castRingHom ℚ) =
        realSubfieldPolynomialRat := rfl
    _ = minpoly ℚ alpha := realSubfieldPolynomialRat_eq_minpoly_alpha
    _ = (minpoly ℤ alpha).map (Int.castRingHom ℚ) := by
      rw [← hcast]
      exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ
        alpha_isIntegral_int

theorem algebra_adjoin_alpha_eq_top :
    Algebra.adjoin ℚ ({alpha} : Set K23plus) = ⊤ :=
  Algebra.adjoin_eq_top_of_primitive_element
    alpha_isIntegral_rat.isAlgebraic adjoin_alpha_eq_top

/-- The power basis `1, alpha, ..., alpha^10` of the maximal real subfield. -/
noncomputable def alphaPowerBasis : PowerBasis ℚ K23plus :=
  PowerBasis.ofAdjoinEqTop alpha_isIntegral_rat
    algebra_adjoin_alpha_eq_top

@[simp]
theorem alphaPowerBasis_gen : alphaPowerBasis.gen = alpha := by
  simp [alphaPowerBasis]

@[simp]
theorem alphaPowerBasis_dim : alphaPowerBasis.dim = 11 := by
  simp [alphaPowerBasis, minpoly_alpha_natDegree]

theorem alphaPowerBasis_minpoly :
    minpoly ℚ alphaPowerBasis.gen = realSubfieldPolynomialRat := by
  rw [alphaPowerBasis_gen, realSubfieldPolynomialRat_eq_minpoly_alpha]

/-- The translated generator whose minimal polynomial is 23-Eisenstein. -/
def beta : K23plus := alpha + 2

theorem beta_isIntegral_int : IsIntegral ℤ beta := by
  exact alpha_isIntegral_int.add (isIntegral_natCast 2)

theorem beta_isIntegral_rat : IsIntegral ℚ beta := by
  exact alpha_isIntegral_rat.add isIntegral_algebraMap

theorem minpoly_rat_beta_eq_shiftedRealSubfieldPolynomial_map :
    minpoly ℚ beta =
      shiftedRealSubfieldPolynomial.map (Int.castRingHom ℚ) := by
  calc
    minpoly ℚ beta =
        (minpoly ℚ alpha).comp (Polynomial.X - Polynomial.C (2 : ℚ)) := by
      simpa [beta] using minpoly.add_algebraMap alpha (2 : ℚ)
    _ = realSubfieldPolynomialRat.comp
        (Polynomial.X - Polynomial.C (2 : ℚ)) := by
      rw [realSubfieldPolynomialRat_eq_minpoly_alpha]
    _ = (realSubfieldPolynomial.comp
        (Polynomial.X - Polynomial.C (2 : ℤ))).map
          (Int.castRingHom ℚ) := by
      rw [Polynomial.map_comp]
      change (realSubfieldPolynomial.map (Int.castRingHom ℚ)).comp
          (Polynomial.X - Polynomial.C (2 : ℚ)) =
        (realSubfieldPolynomial.map (Int.castRingHom ℚ)).comp
          ((Polynomial.X - Polynomial.C (2 : ℤ)).map
            (Int.castRingHom ℚ))
      congr 1
      ext n
      cases n <;> simp
    _ = shiftedRealSubfieldPolynomial.map (Int.castRingHom ℚ) := by
      rw [← shiftedRealSubfieldPolynomial_eq_comp]

theorem minpoly_int_beta_eq_shiftedRealSubfieldPolynomial :
    minpoly ℤ beta = shiftedRealSubfieldPolynomial := by
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have hcast : algebraMap ℤ ℚ = Int.castRingHom ℚ :=
    RingHom.ext_int _ _
  calc
    (minpoly ℤ beta).map (Int.castRingHom ℚ) = minpoly ℚ beta := by
      rw [← hcast]
      exact (minpoly.isIntegrallyClosed_eq_field_fractions' ℚ
        beta_isIntegral_int).symm
    _ = shiftedRealSubfieldPolynomial.map (Int.castRingHom ℚ) :=
      minpoly_rat_beta_eq_shiftedRealSubfieldPolynomial_map

theorem minpoly_beta_natDegree : (minpoly ℚ beta).natDegree = 11 := by
  rw [minpoly_rat_beta_eq_shiftedRealSubfieldPolynomial_map,
    shiftedRealSubfieldPolynomial_monic.natDegree_map,
    shiftedRealSubfieldPolynomial_natDegree]

theorem beta_adjoin_eq_top :
    IntermediateField.adjoin ℚ ({beta} : Set K23plus) =
      (⊤ : IntermediateField ℚ K23plus) := by
  apply IntermediateField.eq_of_le_of_finrank_eq le_top
  rw [IntermediateField.adjoin.finrank beta_isIntegral_rat,
    minpoly_beta_natDegree, IntermediateField.finrank_top',
    maximalRealSubfield_finrank]

theorem algebra_adjoin_beta_eq_top :
    Algebra.adjoin ℚ ({beta} : Set K23plus) = ⊤ :=
  Algebra.adjoin_eq_top_of_primitive_element
    beta_isIntegral_rat.isAlgebraic beta_adjoin_eq_top

/-- The power basis generated by the 23-Eisenstein element `beta = alpha + 2`. -/
noncomputable def betaPowerBasis : PowerBasis ℚ K23plus :=
  PowerBasis.ofAdjoinEqTop beta_isIntegral_rat algebra_adjoin_beta_eq_top

@[simp]
theorem betaPowerBasis_gen : betaPowerBasis.gen = beta := by
  simp [betaPowerBasis]

@[simp]
theorem betaPowerBasis_dim : betaPowerBasis.dim = 11 := by
  simp [betaPowerBasis, minpoly_beta_natDegree]

theorem betaPowerBasis_minpoly_int :
    minpoly ℤ betaPowerBasis.gen = shiftedRealSubfieldPolynomial := by
  rw [betaPowerBasis_gen, minpoly_int_beta_eq_shiftedRealSubfieldPolynomial]

theorem betaPowerBasis_minpoly_rat :
    minpoly ℚ betaPowerBasis.gen =
      shiftedRealSubfieldPolynomial.map (Int.castRingHom ℚ) := by
  rw [betaPowerBasis_gen,
    minpoly_rat_beta_eq_shiftedRealSubfieldPolynomial_map]

/-- For a separable field extension with a power basis, the norm of a
polynomial in the generator is the corresponding resultant. -/
theorem norm_aeval_eq_resultant {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) (g : K[X]) :
    Algebra.norm K (aeval pb.gen g) =
      (minpoly K pb.gen).resultant g := by
  let E := AlgebraicClosure K
  letI := Classical.decEq E
  apply (algebraMap K E).injective
  rw [Algebra.norm_eq_prod_embeddings K E]
  rw [← Polynomial.resultant_map_map]
  rw [← (minpoly.monic pb.isIntegral_gen).natDegree_map
    (algebraMap K E)]
  rw [Polynomial.resultant_eq_prod_eval]
  · have hmonic :
        ((minpoly K pb.gen).map (algebraMap K E)).Monic :=
      (minpoly.monic pb.isIntegral_gen).map (algebraMap K E)
    rw [hmonic.leadingCoeff, one_pow, one_mul]
    rw [@Fintype.prod_equiv (L →ₐ[K] E) _ _ _ _ _
      pb.liftEquiv' (fun σ => σ (aeval pb.gen g))
      (fun x => (g.map (algebraMap K E)).eval x) (by
        intro σ
        simpa only [PowerBasis.liftEquiv'_apply_coe, aeval_def,
          eval₂_eq_eval_map] using
            (aeval_algHom_apply σ pb.gen g).symm)]
    rw [aroots_def, Finset.prod_mem_multiset,
      Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr]
    · have hsep : (minpoly K pb.gen).Separable :=
        Algebra.IsSeparable.isSeparable K pb.gen
      exact nodup_roots
        (hsep.map : ((minpoly K pb.gen).map
          (algebraMap K E)).Separable)
    · intro x
      rfl
  · simp
  · exact IsAlgClosed.splits _

/-- The discriminant of the `alpha` power basis is the polynomial
discriminant of its explicit minimal polynomial. -/
theorem alphaPowerBasis_discr_eq_polynomial_discr :
    Algebra.discr ℚ alphaPowerBasis.basis =
      realSubfieldPolynomialRat.discr := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [norm_aeval_eq_resultant]
  rw [alphaPowerBasis_minpoly]
  have hfinrank : Module.finrank ℚ K23plus = 11 :=
    maximalRealSubfield_finrank
  rw [hfinrank]
  let f := realSubfieldPolynomialRat
  have hmonic : f.Monic := by
    exact realSubfieldPolynomial_monic.map (Int.castRingHom ℚ)
  have hdegree : f.natDegree = 11 := by
    dsimp [f, realSubfieldPolynomialRat]
    rw [realSubfieldPolynomial_monic.natDegree_map,
      realSubfieldPolynomial_natDegree]
  have hdegree_pos : 0 < f.degree := by
    rw [← natDegree_pos_iff_degree_pos, hdegree]
    norm_num
  change (-1 : ℚ) ^ (11 * (11 - 1) / 2) *
      f.resultant f.derivative f.natDegree f.derivative.natDegree =
        f.discr
  rw [Polynomial.natDegree_derivative]
  rw [Polynomial.resultant_deriv hdegree_pos]
  rw [hdegree, hmonic.leadingCoeff]
  norm_num

/-- The discriminant of the `beta` power basis is the polynomial
discriminant of its explicit minimal polynomial. -/
theorem betaPowerBasis_discr_eq_polynomial_discr :
    Algebra.discr ℚ betaPowerBasis.basis =
      (shiftedRealSubfieldPolynomial.map (Int.castRingHom ℚ)).discr := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [norm_aeval_eq_resultant]
  rw [betaPowerBasis_minpoly_rat]
  have hfinrank : Module.finrank ℚ K23plus = 11 :=
    maximalRealSubfield_finrank
  rw [hfinrank]
  let f := shiftedRealSubfieldPolynomial.map (Int.castRingHom ℚ)
  have hmonic : f.Monic :=
    shiftedRealSubfieldPolynomial_monic.map (Int.castRingHom ℚ)
  have hdegree : f.natDegree = 11 := by
    dsimp [f]
    rw [shiftedRealSubfieldPolynomial_monic.natDegree_map,
      shiftedRealSubfieldPolynomial_natDegree]
  have hdegree_pos : 0 < f.degree := by
    rw [← natDegree_pos_iff_degree_pos, hdegree]
    norm_num
  change (-1 : ℚ) ^ (11 * (11 - 1) / 2) *
      f.resultant f.derivative f.natDegree f.derivative.natDegree =
        f.discr
  rw [Polynomial.natDegree_derivative]
  rw [Polynomial.resultant_deriv hdegree_pos]
  rw [hdegree, hmonic.leadingCoeff]
  norm_num

theorem smul_pow_twentyThree (x : K23plus) :
    ((23 : ℚ) ^ 10) • x = (23 : ℤ) ^ 10 • x := by
  rw [Algebra.smul_def, zsmul_eq_mul]
  change (algebraMap ℚ K23plus ((23 : ℚ) ^ 10)) * x =
    (algebraMap ℤ K23plus ((23 : ℤ) ^ 10)) * x
  rw [IsScalarTower.algebraMap_apply ℤ ℚ K23plus, map_pow]
  norm_num

/-- The exact discriminant value implies that the order generated by `beta`
is the full integral closure of `ℤ` in the real subfield. -/
theorem isIntegralClosure_adjoin_beta_of_discr
    (hdisc : Algebra.discr ℚ betaPowerBasis.basis = (23 : ℚ) ^ 10) :
    IsIntegralClosure (Algebra.adjoin ℤ ({beta} : Set K23plus)) ℤ
      K23plus := by
  refine ⟨Subtype.val_injective,
    @fun x => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  swap
  · rintro ⟨y, rfl⟩
    exact IsIntegral.algebraMap
      ((le_integralClosure_iff_isIntegral.1
        (adjoin_le_integralClosure beta_isIntegral_int)).isIntegral y)
  · have hint : IsIntegral ℤ betaPowerBasis.gen := by
      rw [betaPowerBasis_gen]
      exact beta_isIntegral_int
    have H := Algebra.discr_mul_isIntegral_mem_adjoin ℚ hint h
    rw [hdisc] at H
    have H' :
        (23 : ℤ) ^ 10 • x ∈
          Algebra.adjoin ℤ ({betaPowerBasis.gen} : Set K23plus) := by
      rw [← smul_pow_twentyThree]
      exact H
    have hmin :
        (minpoly ℤ betaPowerBasis.gen).IsEisensteinAt
          (Submodule.span ℤ {(23 : ℤ)}) := by
      rw [betaPowerBasis_gen,
        minpoly_int_beta_eq_shiftedRealSubfieldPolynomial]
      exact shiftedRealSubfieldPolynomial_isEisensteinAt
    simpa only [betaPowerBasis_gen] using
      (mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
        (p := (23 : ℤ)) (n := 10)
        (Nat.prime_iff_prime_int.1
          BealRegular.TwentyThreePrimeTwoCube.prime_twentyThree)
        hint h H' hmin)

end


end BealRegular.TwentyThreeRealSubfieldPowerBasis
