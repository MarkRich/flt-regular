import BealRegular.AdjoinRootBaseChange
import BealRegular.Signature357LargeFactorRigidity
import BealRegular.Signature357ModelFactorAlgebras
import Mathlib.Algebra.Algebra.Prod

/-!
# P-adic identification of the signature `(3,5,7)` large factors

This module extends the integral large-factor equivalences from
`Signature357LargeFactorRigidity` to the p-adic numbers.  After removing the
unit normalization, the degree-two and degree-four lifted factor algebras are
identified with the fixed `psi` and `Psi` model algebras.  Composing these
equivalences with the existing Chinese-remainder decompositions replaces the
large existential factor algebra by its fixed model in both critical residue
branches.

These are abstract algebra equivalences.  They do not identify the lifted
polynomial with `psi` or `Psi`, match distinguished roots, identify or rescale
the non-etale degree-five or degree-three factor, classify ramification,
exclude signature `(3,5,7)`, or prove Beal's conjecture.
-/

namespace BealRegular.Signature357LargeFactorBaseChange

open Polynomial

open AdjoinRootBaseChange
open Signature357BranchNormalForms
open Signature357LargeFactorRigidity
open Signature357ModelFactorAlgebras
open Signature357PadicModelUnits
open Signature357ResidualMonicModels

noncomputable section

variable {p : ℕ} [Fact p.Prime]

private theorem normalizedQuadraticModel_map_padic_associated
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    Associated
      ((normalizedQuadraticModel (p := p)).map
        (algebraMap ℤ_[p] ℚ_[p]))
      (psiK (K := ℚ_[p])) := by
  rw [normalizedQuadraticModel, Polynomial.map_mul, Polynomial.map_C,
    algebraMap_ringInverse_fifteen hp3 hp5 hp7]
  have hunit : IsUnit (C (15 : ℚ_[p])⁻¹ : ℚ_[p][X]) := by
    rw [isUnit_C, isUnit_iff_ne_zero]
    exact inv_ne_zero (by norm_num)
  simpa [quadraticIntegralModel, psiK] using
    (associated_unit_mul_left (psiK (K := ℚ_[p]))
      (C (15 : ℚ_[p])⁻¹) hunit)

private theorem normalizedQuarticModel_map_padic_associated
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    Associated
      ((normalizedQuarticModel (p := p)).map
        (algebraMap ℤ_[p] ℚ_[p]))
      (PsiK (K := ℚ_[p])) := by
  rw [normalizedQuarticModel, Polynomial.map_mul, Polynomial.map_C,
    algebraMap_ringInverse_fifteen hp3 hp5 hp7]
  have hunit : IsUnit (C (15 : ℚ_[p])⁻¹ : ℚ_[p][X]) := by
    rw [isUnit_C, isUnit_iff_ne_zero]
    exact inv_ne_zero (by norm_num)
  simpa [quarticIntegralModel, PsiK] using
    (associated_unit_mul_left (PsiK (K := ℚ_[p]))
      (C (15 : ℚ_[p])⁻¹) hunit)

/-- A lifted degree-two factor with the prescribed reduction has p-adic
adjoin-root algebra isomorphic to the fixed quadratic model algebra. -/
def quadraticLargeFactorPadicAlgEquiv
    (f : MonicDegreeEq ℤ_[p] 2)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (hred : f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      zeroQuadraticResidual hp3 hp5 hp7) :
    AdjoinRoot (f.1.map (algebraMap ℤ_[p] ℚ_[p])) ≃ₐ[ℚ_[p]]
      QuadraticFactorAlgebra (K := ℚ_[p]) :=
  (adjoinRootMapAlgEquivOfAlgEquiv (S := ℚ_[p])
    (quadraticLargeFactorAlgEquiv f hp3 hp5 hp7 hred)).trans <|
      AdjoinRoot.algEquivOfAssociated ℚ_[p]
        ((normalizedQuadraticModel (p := p)).map
          (algebraMap ℤ_[p] ℚ_[p]))
        (psiK (K := ℚ_[p]))
        (normalizedQuadraticModel_map_padic_associated hp3 hp5 hp7)

/-- A lifted degree-four factor with the prescribed reduction has p-adic
adjoin-root algebra isomorphic to the fixed quartic model algebra. -/
def quarticLargeFactorPadicAlgEquiv
    (f : MonicDegreeEq ℤ_[p] 4)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (hred : f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      oneQuarticResidual hp3 hp5 hp7) :
    AdjoinRoot (f.1.map (algebraMap ℤ_[p] ℚ_[p])) ≃ₐ[ℚ_[p]]
      QuarticFactorAlgebra (K := ℚ_[p]) :=
  (adjoinRootMapAlgEquivOfAlgEquiv (S := ℚ_[p])
    (quarticLargeFactorAlgEquiv f hp3 hp5 hp7 hred)).trans <|
      AdjoinRoot.algEquivOfAssociated ℚ_[p]
        ((normalizedQuarticModel (p := p)).map
          (algebraMap ℤ_[p] ℚ_[p]))
        (PsiK (K := ℚ_[p]))
        (normalizedQuarticModel_map_padic_associated hp3 hp5 hp7)

/-- On the zero branch, the degree-two factor in the p-adic CRT decomposition
is the fixed quadratic model algebra. -/
theorem zeroBranch_exists_fixedLargeFactor_padicDecomposition
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
            QuadraticFactorAlgebra (K := ℚ_[p]) ×
              AdjoinRoot (g.1.map (algebraMap ℤ_[p] ℚ_[p]))) := by
  obtain ⟨f, g, hfg, hcop, hf0, hg0, ⟨hdecomp⟩⟩ :=
    zeroBranch_exists_factorization_and_padicDecomposition
      u hu hp3 hp5 hp7
  refine ⟨f, g, hfg, hcop, hf0, hg0, ⟨?_⟩⟩
  exact hdecomp.trans <|
    AlgEquiv.prodCongr
      (quadraticLargeFactorPadicAlgEquiv f hp3 hp5 hp7 hf0)
      (AlgEquiv.refl :
        AdjoinRoot (g.1.map (algebraMap ℤ_[p] ℚ_[p])) ≃ₐ[ℚ_[p]]
          AdjoinRoot (g.1.map (algebraMap ℤ_[p] ℚ_[p])))

/-- On the one branch, the degree-four factor in the p-adic CRT decomposition
is the fixed quartic model algebra. -/
theorem oneBranch_exists_fixedLargeFactor_padicDecomposition
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
            QuarticFactorAlgebra (K := ℚ_[p]) ×
              AdjoinRoot (g.1.map (algebraMap ℤ_[p] ℚ_[p]))) := by
  obtain ⟨f, g, hfg, hcop, hf0, hg0, ⟨hdecomp⟩⟩ :=
    oneBranch_exists_factorization_and_padicDecomposition
      u hu hp3 hp5 hp7
  refine ⟨f, g, hfg, hcop, hf0, hg0, ⟨?_⟩⟩
  exact hdecomp.trans <|
    AlgEquiv.prodCongr
      (quarticLargeFactorPadicAlgEquiv f hp3 hp5 hp7 hf0)
      (AlgEquiv.refl :
        AdjoinRoot (g.1.map (algebraMap ℤ_[p] ℚ_[p])) ≃ₐ[ℚ_[p]]
          AdjoinRoot (g.1.map (algebraMap ℤ_[p] ℚ_[p])))

end

end BealRegular.Signature357LargeFactorBaseChange
