import BealRegular.Signature357BranchNormalForms
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exact critical-fiber decompositions for signature `(3,5,7)`

This module uses the Chinese remainder theorem to decompose the quotient
algebras at the two critical parameters `u = 0` and `u = 1`.  Translation by
one relates the latter fiber to the factorization involving the paper's
quartic `Psi`.

These are decompositions of the exact, nonreduced critical fibers.  They do not
identify nearby p-adic fibers with these products and do not prove the
structural-stability or valuation-theoretic claims in Dahmen--Siksek
Proposition 3.3.
-/

namespace BealRegular.Signature357CriticalFiberDecomposition

open Polynomial

open Signature357GenericLocalPolynomial
open Signature357BranchNormalForms

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The two-ideal Chinese remainder equivalence, promoted from rings to
algebras over the coefficient field. -/
private def quotientMulAlgEquivQuotientProd (I J : Ideal K[X])
    (hIJ : IsCoprime I J) :
    (K[X] ⧸ I * J) ≃ₐ[K] (K[X] ⧸ I) × (K[X] ⧸ J) :=
  AlgEquiv.ofRingEquiv
    (f := Ideal.quotientMulEquivQuotientProd I J hIJ) (by
      intro k
      rfl)

omit [CharZero K] in
private theorem fiberK_zero_factorization :
    fiberK (K := K) 0 = X ^ 5 * psiK := by
  simpa using fiveBranch_normalForm (K := K) 0 0

omit [CharZero K] in
private theorem translated_fiberK_one_factorization :
    (fiberK (K := K) 1).comp (X + C 1) = X ^ 3 * PsiK := by
  simpa using threeBranch_translated_normalForm (K := K) 0 0

private theorem psiK_isCoprime_X :
    IsCoprime (psiK (K := K)) X := by
  refine ⟨C (21 : K)⁻¹,
    -(C (21 : K)⁻¹ * (15 * X - 35)), ?_⟩
  simp [psiK]
  field_simp
  ring_nf
  rw [← C_ofNat, ← C_mul]
  norm_num

private theorem PsiK_isCoprime_X :
    IsCoprime (PsiK (K := K)) X := by
  refine ⟨C (35 : K)⁻¹,
    -(C (35 : K)⁻¹ *
      (15 * X ^ 3 + 70 * X ^ 2 + 126 * X + 105)), ?_⟩
  simp [PsiK]
  field_simp
  ring_nf
  rw [← C_ofNat, ← C_mul]
  norm_num

/-- At the exact parameter `u = 0`, the fiber quotient is the product of its
quadratic and fifth-power primary factors. -/
def fiberKZeroDecomposition :
    AdjoinRoot (fiberK (K := K) 0) ≃ₐ[K]
      AdjoinRoot (psiK (K := K)) ×
        AdjoinRoot ((X : K[X]) ^ 5) := by
  have hpoly : IsCoprime (psiK (K := K)) ((X : K[X]) ^ 5) :=
    psiK_isCoprime_X.pow_right
  have hideals : IsCoprime
      (Ideal.span {psiK (K := K)})
      (Ideal.span {(X : K[X]) ^ 5}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hpoly
  have hspan : Ideal.span {fiberK (K := K) 0} =
      Ideal.span {psiK (K := K)} * Ideal.span {(X : K[X]) ^ 5} := by
    rw [fiberK_zero_factorization,
      Ideal.span_singleton_mul_span_singleton]
    simp [mul_comm]
  exact (Ideal.quotientEquivAlgOfEq K hspan).trans
    (quotientMulAlgEquivQuotientProd _ _ hideals)

/-- After translating `T` to `T + 1`, the exact `u = 1` fiber quotient splits
into its quartic and cubic-primary factors. -/
def translatedFiberKOneDecomposition :
    AdjoinRoot ((fiberK (K := K) 1).comp (X + C 1)) ≃ₐ[K]
      AdjoinRoot (PsiK (K := K)) ×
        AdjoinRoot ((X : K[X]) ^ 3) := by
  have hpoly : IsCoprime (PsiK (K := K)) ((X : K[X]) ^ 3) :=
    PsiK_isCoprime_X.pow_right
  have hideals : IsCoprime
      (Ideal.span {PsiK (K := K)})
      (Ideal.span {(X : K[X]) ^ 3}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hpoly
  have hspan : Ideal.span {(fiberK (K := K) 1).comp (X + C 1)} =
      Ideal.span {PsiK (K := K)} * Ideal.span {(X : K[X]) ^ 3} := by
    rw [translated_fiberK_one_factorization,
      Ideal.span_singleton_mul_span_singleton]
    simp [mul_comm]
  exact (Ideal.quotientEquivAlgOfEq K hspan).trans
    (quotientMulAlgEquivQuotientProd _ _ hideals)

/-- Translation by one identifies the original `u = 1` quotient with its
translated presentation. -/
def fiberKOneTranslationEquiv :
    AdjoinRoot (fiberK (K := K) 1) ≃ₐ[K]
      AdjoinRoot ((fiberK (K := K) 1).comp (X + C 1)) := by
  let e : K[X] ≃ₐ[K] K[X] := algEquivAevalXAddC 1
  have hmap : Ideal.span {(fiberK (K := K) 1).comp (X + C 1)} =
      (Ideal.span {fiberK (K := K) 1}).map (e : K[X] →+* K[X]) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  exact Ideal.quotientEquivAlg
    (Ideal.span {fiberK (K := K) 1})
    (Ideal.span {(fiberK (K := K) 1).comp (X + C 1)}) e hmap

/-- Consequently, the original exact `u = 1` fiber quotient itself has the
quartic-by-cubic-primary product decomposition. -/
def fiberKOneDecomposition :
    AdjoinRoot (fiberK (K := K) 1) ≃ₐ[K]
      AdjoinRoot (PsiK (K := K)) ×
        AdjoinRoot ((X : K[X]) ^ 3) :=
  fiberKOneTranslationEquiv.trans translatedFiberKOneDecomposition

end


end BealRegular.Signature357CriticalFiberDecomposition
