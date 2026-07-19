import BealRegular.AdjoinRootBaseChange
import BealRegular.AdjoinRootEtale
import BealRegular.Signature357GlobalFiberCompletions
import BealRegular.Signature357SmallBinomialRigidity
import Mathlib.RingTheory.Unramified.Locus

/-!
# Finite-etale integral models on critical signature `(3,5,7)` branches

This module first packages the generic fiber of the integral binomial model
`X^n - b`.  When `b` is a p-adic unit and `p ∤ n`, the integral adjoin-root
algebra is finite etale over `ℤ_[p]`, is unramified above `(p)`, and has the
expected p-adic binomial algebra as generic fiber.

The first critical-branch application treats a prime dividing `C`.  The
septic completion previously identified with
`X^7 - 1 / (15 * B^2)` is now exhibited as the generic fiber of the explicit
integral binomial model with the same parameter.

This is a local good-reduction result.  It does not yet give analogous
product integral models for the `p ∣ A` and `p ∣ B` branches, handle the
exceptional primes `3`, `5`, or `7`, assert irreducibility or fieldhood,
identify global rings of integers or discriminants, exclude signature
`(3,5,7)`, or prove Beal's conjecture.
-/

namespace BealRegular.Signature357CriticalFiniteEtale

open Polynomial
open scoped Ring TensorProduct

open AdjoinRootBaseChange
open AdjoinRootEtale
open Signature357GlobalFiberCompletions
open Signature357ModelFactorAlgebras
open Signature357PadicModelUnits
open Signature357ResidualMonicModels
open Signature357SmallBinomialRigidity

noncomputable section

/-- The generic fiber of the integral binomial model is the corresponding
p-adic binomial-model algebra.  This statement needs no unit or separability
hypothesis. -/
def binomialIntegralModelGenericFiberEquiv
    {p n : ℕ} [Fact p.Prime] (b : ℤ_[p]) :
    (ℚ_[p] ⊗[ℤ_[p]] AdjoinRoot (binomialIntegralModel n b)) ≃ₐ[ℚ_[p]]
      BinomialModelAlgebra n (algebraMap ℤ_[p] ℚ_[p] b) := by
  have hmap :
      (binomialIntegralModel n b).map (algebraMap ℤ_[p] ℚ_[p]) =
        X ^ n - C (algebraMap ℤ_[p] ℚ_[p] b) := by
    simp [binomialIntegralModel]
  exact
    (adjoinRootBaseChangeAlgEquiv (S := ℚ_[p])
      (binomialIntegralModel n b)).trans
        (AdjoinRoot.algEquivOfEq ℚ_[p] _ _ hmap)

/-- A unit parameter and `p ∤ n` make the integral binomial model finite
etale over the p-adic integers. -/
theorem binomialIntegralModel_finiteEtale
    {p n : ℕ} [Fact p.Prime] (b : ℤ_[p])
    (hb : IsUnit b) (hpn : ¬p ∣ n) :
    Module.Finite ℤ_[p] (AdjoinRoot (binomialIntegralModel n b)) ∧
      Algebra.Etale ℤ_[p] (AdjoinRoot (binomialIntegralModel n b)) := by
  have hn : 0 < n := Nat.pos_of_ne_zero <| by
    intro hn0
    apply hpn
    rw [hn0]
    exact dvd_zero p
  exact adjoinRoot_finiteEtale_of_monic_isCoprime
    (binomialIntegralModel n b)
    (binomialIntegralModel_monic b hn)
    (binomialIntegralModel_isCoprime_derivative hb hpn)

/-- Every prime of the integral binomial model above the p-adic maximal ideal
is unramified. -/
theorem binomialIntegralModel_isUnramifiedIn_padicIdeal
    {p n : ℕ} [Fact p.Prime] (b : ℤ_[p])
    (hb : IsUnit b) (hpn : ¬p ∣ n) :
    Algebra.IsUnramifiedIn (AdjoinRoot (binomialIntegralModel n b))
      (padicIdeal (p := p)) := by
  have hEtale := (binomialIntegralModel_finiteEtale b hb hpn).2
  letI : Algebra.Etale ℤ_[p]
      (AdjoinRoot (binomialIntegralModel n b)) := hEtale
  haveI : Algebra.FormallyUnramified ℤ_[p]
      (AdjoinRoot (binomialIntegralModel n b)) := inferInstance
  intro P hP _
  exact (Algebra.formallyUnramified_iff_forall.mp
    (inferInstance : Algebra.FormallyUnramified ℤ_[p]
      (AdjoinRoot (binomialIntegralModel n b)))) ⟨P, hP⟩

/-- Reusable package: finite-etale integral model, unramifiedness above `(p)`,
and identification of its generic fiber. -/
theorem binomialModel_hasFiniteEtaleIntegralModel
    {p n : ℕ} [Fact p.Prime] (b : ℤ_[p])
    (hb : IsUnit b) (hpn : ¬p ∣ n) :
    (Module.Finite ℤ_[p] (AdjoinRoot (binomialIntegralModel n b)) ∧
      Algebra.Etale ℤ_[p] (AdjoinRoot (binomialIntegralModel n b))) ∧
    Algebra.IsUnramifiedIn (AdjoinRoot (binomialIntegralModel n b))
      (padicIdeal (p := p)) ∧
    Nonempty
      ((ℚ_[p] ⊗[ℤ_[p]] AdjoinRoot (binomialIntegralModel n b)) ≃ₐ[ℚ_[p]]
        BinomialModelAlgebra n (algebraMap ℤ_[p] ℚ_[p] b)) := by
  exact ⟨binomialIntegralModel_finiteEtale b hb hpn,
    binomialIntegralModel_isUnramifiedIn_padicIdeal b hb hpn,
    ⟨binomialIntegralModelGenericFiberEquiv b⟩⟩

/-- The integral septic parameter occurring at the branch `p ∣ C`. -/
def sevenBranchIntegralParameter {p : ℕ} [Fact p.Prime] (B : ℕ) : ℤ_[p] :=
  (15 : ℤ_[p])⁻¹ʳ * ((B : ℤ_[p])⁻¹ʳ) ^ 2

private theorem natCast_isUnit_of_not_dvd
    {p n : ℕ} [Fact p.Prime] (hn : ¬p ∣ n) :
    IsUnit (n : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hn

/-- At every nonexceptional prime dividing `C`, the septic completion of the
global fiber is the generic fiber of an explicit finite-etale, unramified
integral model. -/
theorem globalFiberCompletion_of_prime_dvd_C_hasFiniteEtaleModel
    {p B C : ℕ} [Fact p.Prime]
    (hC : C ≠ 0) (hBC : Nat.Coprime B C) (hpC : p ∣ C)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (Module.Finite ℤ_[p]
        (AdjoinRoot
          (binomialIntegralModel 7
            (sevenBranchIntegralParameter (p := p) B))) ∧
      Algebra.Etale ℤ_[p]
        (AdjoinRoot
          (binomialIntegralModel 7
            (sevenBranchIntegralParameter (p := p) B)))) ∧
    Algebra.IsUnramifiedIn
      (AdjoinRoot
        (binomialIntegralModel 7
          (sevenBranchIntegralParameter (p := p) B)))
      (padicIdeal (p := p)) ∧
    Nonempty
      ((ℚ_[p] ⊗[ℚ] GlobalFiberAlgebra B C) ≃ₐ[ℚ_[p]]
        (ℚ_[p] ⊗[ℤ_[p]]
          AdjoinRoot
            (binomialIntegralModel 7
              (sevenBranchIntegralParameter (p := p) B)))) := by
  have hpB : ¬p ∣ B := by
    have hBp : Nat.Coprime B p := Nat.Coprime.of_dvd_right hpC hBC
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hBp.symm
  have hBunit : IsUnit (B : ℤ_[p]) := natCast_isUnit_of_not_dvd hpB
  obtain ⟨h15, -⟩ :=
    quadraticIntegralModel_endpoints_isUnit (p := p) hp3 hp5 hp7
  have h15' : IsUnit (15 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_leadingCoeff] using h15
  have hb : IsUnit (sevenBranchIntegralParameter (p := p) B) := by
    exact h15'.ringInverse.mul (hBunit.ringInverse.pow 2)
  have hpn : ¬p ∣ 7 := by
    intro hp
    exact hp7 ((Nat.prime_dvd_prime_iff_eq
      (Fact.out : p.Prime) Nat.prime_seven).mp hp)
  have hFE := binomialIntegralModel_finiteEtale
    (sevenBranchIntegralParameter (p := p) B) hb hpn
  refine ⟨hFE,
    binomialIntegralModel_isUnramifiedIn_padicIdeal
      (sevenBranchIntegralParameter (p := p) B) hb hpn, ?_⟩
  exact Nonempty.map
    (fun eglobal => eglobal.trans
      (binomialIntegralModelGenericFiberEquiv
        (sevenBranchIntegralParameter (p := p) B)).symm)
    (globalFiberCompletion_of_prime_dvd_C
      hC hBC hpC hp3 hp5 hp7)

end

end BealRegular.Signature357CriticalFiniteEtale
