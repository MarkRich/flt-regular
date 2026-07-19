import BealRegular.AdicEtaleRigidity
import BealRegular.AdjoinRootEtale
import BealRegular.AdjoinRootReduction
import BealRegular.Signature357ResidualMonicModels

/-!
# Adic rigidity of the signature `(3,5,7)` large factors

This module combines residual quotient compatibility, finite etaleness, and
complete-adic rigidity.  Over a Noetherian ring complete for an ideal, two
monic adjoin-root algebras with the same residual polynomial are equivalent
when their defining polynomials are coprime to their derivatives, or when
their discriminants are units.  A local-ring resultant argument also lifts
this coprimality from the residue field, including when the derivative degree
drops in positive characteristic.

For the signature `(3,5,7)` program, the normalized quadratic and quartic
models are separable over the p-adic integers away from `3`, `5`, and `7`.
Consequently, the adjoin-root algebra of every degree-two or degree-four monic
lift with the prescribed residual model is isomorphic, as an integral p-adic
algebra, to the adjoin-root algebra of the fixed model.

This module does not extend those integral equivalences to the p-adic-number
quotient decomposition, identify or rescale the non-etale degree-five and
degree-three factors, prove a Newton-polygon theorem, classify ramification,
exclude signature `(3,5,7)`, or prove Beal's conjecture.
-/

namespace BealRegular.Signature357LargeFactorRigidity

open Polynomial
open Signature357AdicFactorLifting
open Signature357ResidualMonicModels
open AdicEtaleRigidity
open AdjoinRootEtale
open AdjoinRootReduction

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- Generic complete-adic rigidity for two monic adjoin-root algebras whose
reductions are equal and whose discriminants are units. -/
def adjoinRootAlgEquivOfMapEq
    (I : Ideal R) [IsNoetherianRing R] [IsAdicComplete I R]
    (f g : R[X]) (hf : f.Monic) (hg : g.Monic)
    (hfdisc : IsUnit f.discr) (hgdisc : IsUnit g.discr)
    (hred : f.map (Ideal.Quotient.mk I) = g.map (Ideal.Quotient.mk I)) :
    AdjoinRoot f ≃ₐ[R] AdjoinRoot g := by
  have hfet := adjoinRoot_finiteEtale_of_discr_isUnit f hf hfdisc
  have hget := adjoinRoot_finiteEtale_of_discr_isUnit g hg hgdisc
  letI : Module.Finite R (AdjoinRoot f) := hfet.1
  letI : Algebra.Etale R (AdjoinRoot f) := hfet.2
  letI : Module.Finite R (AdjoinRoot g) := hget.1
  letI : Algebra.Etale R (AdjoinRoot g) := hget.2
  let If := I.map (algebraMap R (AdjoinRoot f))
  let Ig := I.map (algebraMap R (AdjoinRoot g))
  letI : IsAdicComplete If (AdjoinRoot f) :=
    finiteAlgebra_isAdicComplete_map_of_noetherian
  letI : IsAdicComplete Ig (AdjoinRoot g) :=
    finiteAlgebra_isAdicComplete_map_of_noetherian
  let ef := quotientAdjoinRootAlgEquiv I f
  let eg := quotientAdjoinRootAlgEquiv I g
  let ered : AdjoinRoot (f.map (Ideal.Quotient.mk I)) ≃ₐ[R]
      AdjoinRoot (g.map (Ideal.Quotient.mk I)) :=
    (AdjoinRoot.algEquivOfEq (R ⧸ I) _ _ hred).restrictScalars R
  exact formallyEtaleEquivOfQuotientEquiv If Ig (ef.trans (ered.trans eg.symm))

/-- The same rigidity statement with coprimality-to-derivative hypotheses,
which are often easier to transfer through a residue field. -/
def adjoinRootAlgEquivOfMapEqIsCoprime
    (I : Ideal R) [IsNoetherianRing R] [IsAdicComplete I R]
    (f g : R[X]) (hf : f.Monic) (hg : g.Monic)
    (hfcop : IsCoprime f f.derivative)
    (hgcop : IsCoprime g g.derivative)
    (hred : f.map (Ideal.Quotient.mk I) = g.map (Ideal.Quotient.mk I)) :
    AdjoinRoot f ≃ₐ[R] AdjoinRoot g := by
  have hfet := adjoinRoot_finiteEtale_of_monic_isCoprime f hf hfcop
  have hget := adjoinRoot_finiteEtale_of_monic_isCoprime g hg hgcop
  letI : Module.Finite R (AdjoinRoot f) := hfet.1
  letI : Algebra.Etale R (AdjoinRoot f) := hfet.2
  letI : Module.Finite R (AdjoinRoot g) := hget.1
  letI : Algebra.Etale R (AdjoinRoot g) := hget.2
  let If := I.map (algebraMap R (AdjoinRoot f))
  let Ig := I.map (algebraMap R (AdjoinRoot g))
  letI : IsAdicComplete If (AdjoinRoot f) :=
    finiteAlgebra_isAdicComplete_map_of_noetherian
  letI : IsAdicComplete Ig (AdjoinRoot g) :=
    finiteAlgebra_isAdicComplete_map_of_noetherian
  let ef := quotientAdjoinRootAlgEquiv I f
  let eg := quotientAdjoinRootAlgEquiv I g
  let ered : AdjoinRoot (f.map (Ideal.Quotient.mk I)) ≃ₐ[R]
      AdjoinRoot (g.map (Ideal.Quotient.mk I)) :=
    (AdjoinRoot.algEquivOfEq (R ⧸ I) _ _ hred).restrictScalars R
  exact formallyEtaleEquivOfQuotientEquiv If Ig (ef.trans (ered.trans eg.symm))

/-- A positive-degree polynomial with unit leading coefficient and unit
discriminant is coprime to its derivative. Monicity is not needed. -/
theorem isCoprime_derivative_of_isUnit_leadingCoeff_discr
    (f : R[X]) (hdeg : 0 < f.degree)
    (hlc : IsUnit f.leadingCoeff) (hdisc : IsUnit f.discr) :
    IsCoprime f f.derivative := by
  have hres : IsUnit
      (resultant f f.derivative f.natDegree (f.natDegree - 1)) := by
    rw [resultant_deriv hdeg]
    exact (((isUnit_one.neg).pow
      (f.natDegree * (f.natDegree - 1) / 2)).mul hlc).mul hdisc
  have hn : f.natDegree ≠ 0 := by
    rw [← Nat.pos_iff_ne_zero, natDegree_pos_iff_degree_pos]
    exact hdeg
  obtain ⟨a, b, -, -, hab⟩ := exists_mul_add_mul_eq_C_resultant
    f f.derivative le_rfl (natDegree_derivative_le f) (Or.inl hn)
  exact ⟨C (hres.unit⁻¹).1 * a, C (hres.unit⁻¹).1 * b, by
    rw [mul_assoc, mul_assoc, ← mul_add]
    rw [mul_comm a f, mul_comm b f.derivative, hab]
    rw [← C_mul, IsUnit.val_inv_mul, C_1]⟩

variable [IsLocalRing R]

omit [IsLocalRing R] in
private theorem resultant_derivative_fixed_eq
    (f : R[X]) (hf : f.Monic) :
    resultant f f.derivative f.natDegree (f.natDegree - 1) =
      resultant f f.derivative := by
  have hle : f.derivative.natDegree ≤ f.natDegree - 1 :=
    natDegree_derivative_le f
  have hsum :
      f.derivative.natDegree +
          ((f.natDegree - 1) - f.derivative.natDegree) =
        f.natDegree - 1 := by omega
  rw [← hsum, resultant_add_right_deg _ _ _ _ _ le_rfl]
  simp [hf.leadingCoeff]

/-- A monic polynomial whose residue is separable is already coprime to its
derivative over a local coefficient ring. The fixed-degree resultant padding
handles derivative-degree collapse in the residue field. -/
theorem isCoprime_derivative_of_residue
    (f : R[X]) (hf : f.Monic)
    (hres : IsCoprime
      (f.map (IsLocalRing.residue R))
      (f.map (IsLocalRing.residue R)).derivative) :
    IsCoprime f f.derivative := by
  rw [← isUnit_resultant_iff_isCoprime hf]
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  have hunit : IsUnit
      ((f.map (IsLocalRing.residue R)).resultant
        (f.map (IsLocalRing.residue R)).derivative) :=
    (isUnit_resultant_iff_isCoprime (hf.map _)).mpr hres
  have hne := hunit.ne_zero
  have hs := resultant_derivative_fixed_eq f hf
  have ht := resultant_derivative_fixed_eq
    (f.map (IsLocalRing.residue R)) (hf.map _)
  rw [← hs]
  rw [← ht] at hne
  rw [hf.natDegree_map, Polynomial.derivative_map] at hne
  rw [Polynomial.resultant_map_map] at hne
  exact hne

/-- Equality with a separable residual model transfers coprimality with the
derivative to a monic lift over a local ring. -/
theorem isCoprime_derivative_of_residue_eq
    (f g : R[X]) (hf : f.Monic)
    (hred : f.map (IsLocalRing.residue R) =
      g.map (IsLocalRing.residue R))
    (hgcop : IsCoprime g g.derivative) :
    IsCoprime f f.derivative := by
  apply isCoprime_derivative_of_residue f hf
  rw [hred]
  have h := hgcop.map (Polynomial.mapRingHom (IsLocalRing.residue R))
  change IsCoprime (g.map (IsLocalRing.residue R))
    (g.derivative.map (IsLocalRing.residue R)) at h
  simpa only [Polynomial.derivative_map] using h

variable {p : ℕ} [Fact p.Prime]

/-- Over the p-adic integers, equal reductions and a separable fixed monic
model give an exact equivalence of the integral adjoin-root algebras. -/
def padicAdjoinRootAlgEquivOfMapEqIsCoprime
    (f g : ℤ_[p][X]) (hf : f.Monic) (hg : g.Monic)
    (hgcop : IsCoprime g g.derivative)
    (hred : f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      g.map (Ideal.Quotient.mk (padicIdeal (p := p)))) :
    AdjoinRoot f ≃ₐ[ℤ_[p]] AdjoinRoot g := by
  letI : IsAdicComplete (padicIdeal (p := p)) ℤ_[p] :=
    padicInt_span_p_isAdicComplete
  have hred' : f.map (IsLocalRing.residue ℤ_[p]) =
      g.map (IsLocalRing.residue ℤ_[p]) := by
    change f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p])) =
      g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[p]))
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact hred
  exact adjoinRootAlgEquivOfMapEqIsCoprime
    (padicIdeal (p := p)) f g hf hg
    (isCoprime_derivative_of_residue_eq f g hf hred' hgcop)
    hgcop hred

open Signature357PadicModelUnits

/-- The normalized quadratic model is coprime to its derivative over the
p-adic integers away from the three exceptional primes. -/
theorem normalizedQuadraticModel_isCoprime_derivative
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    IsCoprime (normalizedQuadraticModel (p := p))
      (normalizedQuadraticModel (p := p)).derivative := by
  obtain ⟨h15lc, -⟩ := quadraticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h15 : IsUnit (15 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_leadingCoeff] using h15lc
  have hPcop : IsCoprime (quadraticIntegralModel (p := p))
      (quadraticIntegralModel (p := p)).derivative := by
    apply isCoprime_derivative_of_isUnit_leadingCoeff_discr
    · rw [← natDegree_pos_iff_degree_pos,
        quadraticIntegralModel_natDegree]
      norm_num
    · exact h15lc
    · exact quadraticIntegralModel_discr_isUnit hp5 hp7
  have hscale : quadraticIntegralModel (p := p) =
      C (15 : ℤ_[p]) * normalizedQuadraticModel (p := p) := by
    rw [normalizedQuadraticModel, ← mul_assoc, ← C_mul,
      Ring.mul_inverse_cancel _ h15, C_1, one_mul]
  rw [hscale, derivative_C_mul] at hPcop
  exact (isCoprime_mul_unit_left (isUnit_C.mpr h15) _ _).mp hPcop

/-- The normalized quartic model is coprime to its derivative over the p-adic
integers away from the three exceptional primes. -/
theorem normalizedQuarticModel_isCoprime_derivative
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    IsCoprime (normalizedQuarticModel (p := p))
      (normalizedQuarticModel (p := p)).derivative := by
  obtain ⟨h15lc, -⟩ := quarticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h15 : IsUnit (15 : ℤ_[p]) := by
    simpa only [quarticIntegralModel_leadingCoeff] using h15lc
  have hPcop : IsCoprime (quarticIntegralModel (p := p))
      (quarticIntegralModel (p := p)).derivative := by
    apply isCoprime_derivative_of_isUnit_leadingCoeff_discr
    · rw [← natDegree_pos_iff_degree_pos,
        quarticIntegralModel_natDegree]
      norm_num
    · exact h15lc
    · exact quarticIntegralModel_discr_isUnit hp3 hp5 hp7
  have hscale : quarticIntegralModel (p := p) =
      C (15 : ℤ_[p]) * normalizedQuarticModel (p := p) := by
    rw [normalizedQuarticModel, ← mul_assoc, ← C_mul,
      Ring.mul_inverse_cancel _ h15, C_1, one_mul]
  rw [hscale, derivative_C_mul] at hPcop
  exact (isCoprime_mul_unit_left (isUnit_C.mpr h15) _ _).mp hPcop

/-- The adjoin-root algebra of a lifted degree-two factor with the prescribed
residual quadratic model is isomorphic over the p-adic integers to the model
adjoin-root algebra. -/
def quadraticLargeFactorAlgEquiv
    (f : MonicDegreeEq ℤ_[p] 2)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (hred : f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      zeroQuadraticResidual hp3 hp5 hp7) :
    AdjoinRoot f.1 ≃ₐ[ℤ_[p]]
      AdjoinRoot (normalizedQuadraticModel (p := p)) := by
  have hredpoly := congrArg Subtype.val hred
  change f.1.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
    (normalizedQuadraticModel (p := p)).map
      (Ideal.Quotient.mk (padicIdeal (p := p))) at hredpoly
  exact padicAdjoinRootAlgEquivOfMapEqIsCoprime
    f.1 (normalizedQuadraticModel (p := p)) f.monic
    (normalizedQuadraticModel_monic hp3 hp5 hp7)
    (normalizedQuadraticModel_isCoprime_derivative hp3 hp5 hp7)
    hredpoly

/-- The adjoin-root algebra of a lifted degree-four factor with the prescribed
residual quartic model is isomorphic over the p-adic integers to the model
adjoin-root algebra. -/
def quarticLargeFactorAlgEquiv
    (f : MonicDegreeEq ℤ_[p] 4)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (hred : f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      oneQuarticResidual hp3 hp5 hp7) :
    AdjoinRoot f.1 ≃ₐ[ℤ_[p]]
      AdjoinRoot (normalizedQuarticModel (p := p)) := by
  have hredpoly := congrArg Subtype.val hred
  change f.1.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
    (normalizedQuarticModel (p := p)).map
      (Ideal.Quotient.mk (padicIdeal (p := p))) at hredpoly
  exact padicAdjoinRootAlgEquivOfMapEqIsCoprime
    f.1 (normalizedQuarticModel (p := p)) f.monic
    (normalizedQuarticModel_monic hp3 hp5 hp7)
    (normalizedQuarticModel_isCoprime_derivative hp3 hp5 hp7)
    hredpoly

end

end BealRegular.Signature357LargeFactorRigidity
