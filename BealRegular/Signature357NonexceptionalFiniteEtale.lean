import BealRegular.Signature357CriticalProductFiniteEtale
import BealRegular.Signature357S0FiniteEtale
import Mathlib.RingTheory.Etale.Finite

/-!
# Finite-etale models at every nonexceptional prime

This module packages the four local branches of a coprime signature `(3,5,7)`
equation into one theorem.  At every prime other than `3`, `5`, and `7`, the
completed rational fiber is the generic fiber of a finite-etale
`ℤ_[p]`-algebra.  The model is explicit within each of the branches `p ∣ A`,
`p ∣ B`, `p ∣ C`, and their common complement.

This is a local existence statement.  It does not identify the model with an
integral closure or ring of integers, classify a global discriminant, assert
that the rational fiber is a field, exclude signature `(3,5,7)`, or prove
Beal's conjecture.
-/

open scoped TensorProduct

namespace BealRegular.Signature357NonexceptionalFiniteEtale

open Signature357CriticalFiniteEtale
open Signature357CriticalProductFiniteEtale
open Signature357GlobalFiberCompletions
open Signature357PadicModelUnits
open Signature357ResidualMonicModels
open Signature357S0FiniteEtale

noncomputable section

/-- A finite-etale `ℤ_[p]`-model whose generic fiber is the completed
signature `(3,5,7)` rational fiber. -/
structure PadicFiniteEtaleModel
    (p B C : ℕ) [Fact p.Prime] where
  /-- The bundled finite-etale integral model. -/
  model : CommAlgCat.FiniteEtale ℤ_[p]
  /-- The chosen integral model is unramified above the p-adic ideal. -/
  unramified : Algebra.IsUnramifiedIn model (padicIdeal (p := p))
  /-- The completed rational fiber is the generic fiber of `model`. -/
  completionEquivGenericFiber :
    (ℚ_[p] ⊗[ℚ] GlobalFiberAlgebra B C) ≃ₐ[ℚ_[p]]
      (ℚ_[p] ⊗[ℤ_[p]] model)

/-- There exists a finite-etale integral model for the completed rational
fiber at `p`. -/
abbrev HasPadicFiniteEtaleModel
    (p B C : ℕ) [Fact p.Prime] : Prop :=
  Nonempty (PadicFiniteEtaleModel p B C)

namespace PadicFiniteEtaleModel

variable {p B C : ℕ} [Fact p.Prime]

/-- The packaged model exposes its module-finiteness instance directly. -/
theorem moduleFinite (M : PadicFiniteEtaleModel p B C) :
    Module.Finite ℤ_[p] M.model := by
  infer_instance

/-- The packaged model exposes its etaleness instance directly. -/
theorem etale (M : PadicFiniteEtaleModel p B C) :
    Algebra.Etale ℤ_[p] M.model := by
  infer_instance

end PadicFiniteEtaleModel

private def packageExplicitModel
    {p B C : ℕ} [Fact p.Prime]
    (M : Type) [CommRing M] [Algebra ℤ_[p] M]
    (hfinite : Module.Finite ℤ_[p] M)
    (hetale : Algebra.Etale ℤ_[p] M)
    (hunramified : Algebra.IsUnramifiedIn M (padicIdeal (p := p)))
    (e : (ℚ_[p] ⊗[ℚ] GlobalFiberAlgebra B C) ≃ₐ[ℚ_[p]]
      (ℚ_[p] ⊗[ℤ_[p]] M)) :
    PadicFiniteEtaleModel p B C := by
  letI : Module.Finite ℤ_[p] M := hfinite
  letI : Algebra.Etale ℤ_[p] M := hetale
  exact
    { model := CommAlgCat.FiniteEtale.of ℤ_[p] M
      unramified := hunramified
      completionEquivGenericFiber := e }

/-- Every prime away from `3`, `5`, and `7` admits a finite-etale integral
model of the completed signature `(3,5,7)` rational fiber.

The cases are the branches `p ∣ A`, `p ∣ B`, `p ∣ C`, and their common
complement.  The result only asserts existence of a local integral model; it
does not identify that model with a global integral closure. -/
theorem globalFiberCompletion_hasFiniteEtaleModel_at_nonexceptionalPrime
    {p A B C : ℕ} [Fact p.Prime]
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hAC : Nat.Coprime A C) (hBC : Nat.Coprime B C)
    (hEq : A ^ 3 + B ^ 5 = C ^ 7)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    HasPadicFiniteEtaleModel p B C := by
  by_cases hpA : p ∣ A
  · have h := globalFiberCompletion_of_prime_dvd_A_hasFiniteEtaleProductModel
      hA hAC hpA hEq hp3 hp5 hp7
    exact h.2.2.map fun e ↦
      packageExplicitModel
        (OneBranchIntegralModel (p := p)
          (oneBranchIntegralParameter (p := p) C))
        h.1.1 h.1.2 h.2.1 e
  by_cases hpB : p ∣ B
  · have h := globalFiberCompletion_of_prime_dvd_B_hasFiniteEtaleProductModel
      hB hBC hpB hp3 hp5 hp7
    exact h.2.2.map fun e ↦
      packageExplicitModel
        (ZeroBranchIntegralModel (p := p)
          (zeroBranchIntegralParameter (p := p) C))
        h.1.1 h.1.2 h.2.1 e
  by_cases hpC : p ∣ C
  · have h := globalFiberCompletion_of_prime_dvd_C_hasFiniteEtaleModel
      hC hBC hpC hp3 hp5 hp7
    exact h.2.2.map fun e ↦
      packageExplicitModel
        (AdjoinRoot
          (binomialIntegralModel 7
            (sevenBranchIntegralParameter (p := p) B)))
        h.1.1 h.1.2 h.2.1 e
  · have h := globalFiberCompletion_s0_hasFiniteEtaleModel
      hpA hpB hpC hEq hp3 hp5 hp7
    exact h.2.2.map fun e ↦
      packageExplicitModel
        (AdjoinRoot
          (normalizedIntegralFiber
            (s0IntegralParameter (p := p) B C)))
        h.1.1 h.1.2 h.2.1 e

end

end BealRegular.Signature357NonexceptionalFiniteEtale
