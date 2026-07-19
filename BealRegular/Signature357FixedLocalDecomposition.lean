import BealRegular.Signature357LargeFactorBaseChange
import BealRegular.Signature357OneBranchDescaledModel
import BealRegular.Signature357ZeroBranchDescaledModel
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Explicit p-adic decompositions near the signature `(3,5,7)` critical branches

Let `p` be different from `3`, `5`, and `7`.  If `q` is a nonzero element of
the maximal ideal of `ℤ_[p]` and `a` is a unit, this module identifies the
adjoin-root algebra of each nearby branch fiber over `ℚ_[p]`:

* at `u = q ^ 5 * a`, it is the product of the fixed quadratic model algebra
  and the binomial model for `X ^ 5 - 21⁻¹ a`;
* at `u = 1 + q ^ 3 * a`, it is the product of the fixed quartic model algebra
  and the binomial model for `X ^ 3 - 35⁻¹ a`.

The proofs compose scalar normalization and, in the second branch, translation
with the previously constructed large-factor and small-factor equivalences.
The equivalences are abstract: they do not preserve distinguished roots
through rigidity, classify ramification or field factors, exclude signature
`(3,5,7)`, or prove Beal's conjecture.
-/

namespace BealRegular.Signature357FixedLocalDecomposition

open Polynomial
open scoped Ring

open Signature357LargeFactorBaseChange
open Signature357ModelFactorAlgebras
open Signature357OneBranchDescaledModel
open Signature357ResidualMonicModels
open Signature357ZeroBranchDescaledModel

noncomputable section

variable {p : ℕ} [Fact p.Prime]

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

private def adjoinRootTranslateOneEquiv (P : ℚ_[p][X]) :
    AdjoinRoot P ≃ₐ[ℚ_[p]] AdjoinRoot (P.comp (X + C 1)) := by
  let e : ℚ_[p][X] ≃ₐ[ℚ_[p]] ℚ_[p][X] := algEquivAevalXAddC 1
  have hmap : Ideal.span {P.comp (X + C 1)} =
      (Ideal.span {P}).map (e : ℚ_[p][X] →+* ℚ_[p][X]) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  exact Ideal.quotientEquivAlg
    (Ideal.span {P}) (Ideal.span {P.comp (X + C 1)}) e hmap

/-- The original zero-branch fiber algebra is the fixed quadratic model times
the quintic binomial model with parameter `21⁻¹ a`. -/
theorem zeroBranch_fixedModel_padicDecomposition
    (q a : ℤ_[p]) (ha : IsUnit a) (hq : q ≠ 0)
    (hqI : q ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    Nonempty
      (AdjoinRoot
          (Signature357GenericLocalPolynomial.fiberK
            (algebraMap ℤ_[p] ℚ_[p] (q ^ 5 * a))) ≃ₐ[ℚ_[p]]
        QuadraticFactorAlgebra (K := ℚ_[p]) ×
          BinomialModelAlgebra 5
            (algebraMap ℤ_[p] ℚ_[p] ((21 : ℤ_[p])⁻¹ʳ * a))) := by
  have hu : q ^ 5 * a ∈ padicIdeal (p := p) :=
    (padicIdeal (p := p)).mul_mem_right a
      ((padicIdeal (p := p)).pow_mem_of_mem hqI 5 (by omega))
  obtain ⟨f, g, hfac, -, hred, -, ⟨hlarge⟩⟩ :=
    zeroBranch_exists_fixedLargeFactor_padicDecomposition
      (q ^ 5 * a) hu hp3 hp5 hp7
  obtain ⟨G, -, -, ⟨hsmall⟩⟩ :=
    zeroBranch_exists_descaled_quintic_and_binomial_padicEquiv
      q a ha hq hqI hp3 hp5 hp7 f g hfac hred
  exact ⟨(adjoinRootNormalizationEquiv
    (Signature357GenericLocalPolynomial.fiberK
      (algebraMap ℤ_[p] ℚ_[p] (q ^ 5 * a)))).trans
        (hlarge.trans (AlgEquiv.prodCongr AlgEquiv.refl hsmall))⟩

/-- The original translated-one fiber algebra is the fixed quartic model times
the cubic binomial model with parameter `35⁻¹ a`. -/
theorem oneBranch_fixedModel_padicDecomposition
    (q a : ℤ_[p]) (ha : IsUnit a) (hq : q ≠ 0)
    (hqI : q ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    Nonempty
      (AdjoinRoot
          (Signature357GenericLocalPolynomial.fiberK
            (algebraMap ℤ_[p] ℚ_[p] (1 + q ^ 3 * a))) ≃ₐ[ℚ_[p]]
        QuarticFactorAlgebra (K := ℚ_[p]) ×
          BinomialModelAlgebra 3
            (algebraMap ℤ_[p] ℚ_[p] ((35 : ℤ_[p])⁻¹ʳ * a))) := by
  have hpow : q ^ 3 * a ∈ padicIdeal (p := p) :=
    (padicIdeal (p := p)).mul_mem_right a
      ((padicIdeal (p := p)).pow_mem_of_mem hqI 3 (by omega))
  have hu : 1 + q ^ 3 * a - 1 ∈ padicIdeal (p := p) := by
    convert hpow using 1
    ring
  obtain ⟨f, g, hfac, -, hred, -, ⟨hlarge⟩⟩ :=
    oneBranch_exists_fixedLargeFactor_padicDecomposition
      (1 + q ^ 3 * a) hu hp3 hp5 hp7
  obtain ⟨G, -, -, ⟨hsmall⟩⟩ :=
    oneBranch_exists_descaled_cubic_and_binomial_padicEquiv
      q a ha hq hqI hp3 hp5 hp7 f g hfac hred
  let P := Signature357GenericLocalPolynomial.fiberK
    (algebraMap ℤ_[p] ℚ_[p] (1 + q ^ 3 * a))
  exact ⟨(adjoinRootTranslateOneEquiv P).trans
    ((adjoinRootNormalizationEquiv (P.comp (X + C 1))).trans
      (hlarge.trans (AlgEquiv.prodCongr AlgEquiv.refl hsmall)))⟩

end

end BealRegular.Signature357FixedLocalDecomposition
