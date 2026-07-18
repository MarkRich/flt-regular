import BealRegular.Signature357ModelFactorInvariants
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# Quotient algebras for the `(3,5,7)` model factors

This module packages the quadratic `psi`, quartic `Psi`, and generic binomial
`X^n - a` model polynomials as quotient algebras.  The fixed factors and every
positive-degree binomial give finite-dimensional quotients.  For separable
factors, these quotients are finite etale over their coefficient field in the
algebraic-geometric sense of `Algebra.Etale`.

These statements do not identify an original Dahmen--Siksek fiber quotient
with a product of model quotients.  They also do not prove structural
stability, integral-model etaleness, Newton-polygon results, or
valuation-theoretic unramifiedness over a p-adic valuation ring.
-/

namespace BealRegular.Signature357ModelFactorAlgebras

open Polynomial

open Signature357BranchNormalForms
open Signature357ModelFactorInvariants

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private def monicAssociate (f : K[X]) : K[X] :=
  C f.leadingCoeff⁻¹ * f

omit [CharZero K] in
private theorem monicAssociate_associated {f : K[X]} (hf : f ≠ 0) :
    Associated (monicAssociate f) f := by
  apply associated_unit_mul_left
  rw [isUnit_C, isUnit_iff_ne_zero]
  exact inv_ne_zero (leadingCoeff_ne_zero.mpr hf)

omit [CharZero K] in
private theorem monicAssociate_monic {f : K[X]} (hf : f ≠ 0) :
    (monicAssociate f).Monic := by
  rw [Monic, monicAssociate, leadingCoeff_mul]
  simp [hf]

omit [CharZero K] in
private theorem monicAssociate_separable {f : K[X]} (hf : f ≠ 0)
    (hseparable : f.Separable) : (monicAssociate f).Separable :=
  (monicAssociate_associated hf).symm.separable hseparable

private def standardEtalePairOfSeparable {f : K[X]} (hf : f ≠ 0)
    (hseparable : f.Separable) : StandardEtalePair K where
  f := monicAssociate f
  monic_f := monicAssociate_monic hf
  g := 1
  cond := by
    obtain ⟨a, b, hab⟩ := monicAssociate_separable hf hseparable
    exact ⟨b, a, 1, by simpa [mul_comm, add_comm] using hab⟩

private def standardEtaleEquivAdjoinRoot {f : K[X]} (hf : f ≠ 0)
    (hseparable : f.Separable) :
    (standardEtalePairOfSeparable hf hseparable).Ring ≃ₐ[K] AdjoinRoot f :=
  (standardEtalePairOfSeparable hf hseparable).equivAwayAdjoinRoot |>.trans <|
    ((IsLocalization.atUnit
      (AdjoinRoot (monicAssociate f))
      (Localization.Away (AdjoinRoot.mk (monicAssociate f) 1))
      (AdjoinRoot.mk (monicAssociate f) 1) (by simp)).symm.restrictScalars K) |>.trans <|
    AdjoinRoot.algEquivOfAssociated K (monicAssociate f) f
      (monicAssociate_associated hf)

omit [CharZero K] in
private theorem adjoinRoot_etale_of_separable {f : K[X]} (hf : f ≠ 0)
    (hseparable : f.Separable) : Algebra.Etale K (AdjoinRoot f) := by
  let P := standardEtalePairOfSeparable hf hseparable
  let e : P.Ring ≃ₐ[K] AdjoinRoot f :=
    standardEtaleEquivAdjoinRoot hf hseparable
  haveI : Algebra.Etale K P.Ring := inferInstance
  exact Algebra.Etale.of_equiv e

omit [CharZero K] in
private theorem adjoinRoot_finiteEtale_of_separable {f : K[X]} (hf : f ≠ 0)
    (hseparable : f.Separable) :
    Module.Finite K (AdjoinRoot f) ∧ Algebra.Etale K (AdjoinRoot f) :=
  ⟨(AdjoinRoot.powerBasis hf).finite,
    adjoinRoot_etale_of_separable hf hseparable⟩

omit [CharZero K] in
private theorem adjoinRoot_finrank (f : K[X]) :
    Module.finrank K (AdjoinRoot f) = f.natDegree := by
  change Module.finrank K (K[X] ⧸ Ideal.span {f}) = f.natDegree
  exact finrank_quotient_span_eq_natDegree

/-- The quotient by the quadratic factor `psi`. -/
abbrev QuadraticFactorAlgebra := AdjoinRoot (psiK (K := K))

/-- The quotient by the quartic factor `Psi`. -/
abbrev QuarticFactorAlgebra := AdjoinRoot (PsiK (K := K))

/-- The quotient by the generic normalized binomial `X^n - a`. -/
abbrev BinomialModelAlgebra (n : ℕ) (a : K) := AdjoinRoot (X ^ n - C a)

/-- The quadratic factor quotient has dimension two. -/
theorem quadraticFactorAlgebra_finrank :
    Module.finrank K (QuadraticFactorAlgebra (K := K)) = 2 := by
  rw [adjoinRoot_finrank, psiK_natDegree]

/-- The quartic factor quotient has dimension four. -/
theorem quarticFactorAlgebra_finrank :
    Module.finrank K (QuarticFactorAlgebra (K := K)) = 4 := by
  rw [adjoinRoot_finrank, PsiK_natDegree]

omit [CharZero K] in
/-- A positive-degree binomial quotient is finite and has dimension `n`. -/
theorem binomialModelAlgebra_finite_finrank {n : ℕ} (a : K) (hn : 0 < n) :
    Module.Finite K (BinomialModelAlgebra n a) ∧
      Module.finrank K (BinomialModelAlgebra n a) = n := by
  have hf : (X ^ n - C a : K[X]) ≠ 0 := by
    apply ne_zero_of_natDegree_gt (n := 0)
    rw [natDegree_X_pow_sub_C]
    exact hn
  exact ⟨(AdjoinRoot.powerBasis hf).finite, by
    rw [adjoinRoot_finrank, natDegree_X_pow_sub_C]⟩

/-- The quadratic factor quotient is finite etale over its coefficient field. -/
theorem quadraticFactorAlgebra_finiteEtale :
    Module.Finite K (QuadraticFactorAlgebra (K := K)) ∧
      Algebra.Etale K (QuadraticFactorAlgebra (K := K)) := by
  apply adjoinRoot_finiteEtale_of_separable
  · apply ne_zero_of_natDegree_gt (n := 0)
    rw [psiK_natDegree]
    norm_num
  · exact psiK_separable

/-- The quartic factor quotient is finite etale over its coefficient field. -/
theorem quarticFactorAlgebra_finiteEtale :
    Module.Finite K (QuarticFactorAlgebra (K := K)) ∧
      Algebra.Etale K (QuarticFactorAlgebra (K := K)) := by
  apply adjoinRoot_finiteEtale_of_separable
  · apply ne_zero_of_natDegree_gt (n := 0)
    rw [PsiK_natDegree]
    norm_num
  · exact PsiK_separable

/-- A positive-degree binomial with nonzero parameter gives a finite etale
quotient over a characteristic-zero coefficient field. -/
theorem binomialModelAlgebra_finiteEtale {n : ℕ} {a : K}
    (hn : 0 < n) (ha : a ≠ 0) :
    Module.Finite K (BinomialModelAlgebra n a) ∧
      Algebra.Etale K (BinomialModelAlgebra n a) := by
  apply adjoinRoot_finiteEtale_of_separable
  · apply ne_zero_of_natDegree_gt (n := 0)
    rw [natDegree_X_pow_sub_C]
    exact hn
  · exact separable_X_pow_sub_C a (by exact_mod_cast hn.ne') ha

end

end BealRegular.Signature357ModelFactorAlgebras
