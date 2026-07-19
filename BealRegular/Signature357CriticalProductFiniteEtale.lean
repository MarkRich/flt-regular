import BealRegular.Signature357CriticalFiniteEtale
import BealRegular.Signature357LargeFactorBaseChange
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Finite-etale product models on critical signature `(3,5,7)` branches

This module completes the local integral upgrade for the two critical branches
whose p-adic completions split as products.  At a nonexceptional prime dividing
`B`, the completion is the generic fiber of an explicit quadratic-by-quintic
finite-etale `ℤ_[p]`-model.  At a nonexceptional prime dividing `A`, it is the
generic fiber of an explicit quartic-by-cubic model.

The small-factor parameters are exactly

* `1 / (21 * C^2)` on the `p ∣ B` branch, and
* `-1 / (35 * C^4)` on the `p ∣ A` branch.

Thus the second small factor is the polynomial `X^3 + 1 / (35 * C^4)`.

These are completion-level product decompositions.  They do not imply a
factorization of the global rational algebra, identify these integral models
with integral closures or rings of integers, assert irreducibility or
fieldhood, classify a global discriminant, handle the exceptional primes
`3`, `5`, or `7`, exclude signature `(3,5,7)`, or prove Beal's conjecture.
-/

namespace BealRegular.Signature357CriticalProductFiniteEtale

open Polynomial
open scoped Ring TensorProduct

open AdjoinRootBaseChange
open AdjoinRootEtale
open Signature357CriticalFiniteEtale
open Signature357GlobalFiberCompletions
open Signature357LargeFactorBaseChange
open Signature357LargeFactorRigidity
open Signature357ModelFactorAlgebras
open Signature357PadicModelUnits
open Signature357ResidualMonicModels

noncomputable section

universe u

private def twoTypes (A B : Type u) : Fin 2 → Type u :=
  Fin.cases A (fun _ ↦ B)

/-- A binary product of etale algebras is etale.  Mathlib supplies the
dependent finite-product instance; this bridge transports it across the
standard equivalence between a two-entry family and a binary product. -/
private theorem etale_prod
    (R A B : Type u) [cR : CommRing R]
    [cA : CommRing A] [cB : CommRing B]
    [algA : Algebra R A] [algB : Algebra R B]
    [etA : Algebra.Etale R A] [etB : Algebra.Etale R B] :
    Algebra.Etale R (A × B) := by
  let T : Fin 2 → Type u := twoTypes A B
  letI : ∀ i, CommRing (T i) := fun i ↦
    Fin.cases cA (fun _ ↦ cB) i
  letI : ∀ i, Algebra R (T i) := fun i ↦
    Fin.cases algA (fun _ ↦ algB) i
  letI : ∀ i, Algebra.Etale R (T i) := fun i ↦
    Fin.cases etA (fun _ ↦ etB) i
  let e : (∀ i, T i) ≃ₐ[R] A × B :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.piFinTwo T)
      (by intro r; ext <;> rfl)
  exact Algebra.Etale.of_equiv e

variable {p : ℕ} [Fact p.Prime]

private theorem isUnramifiedIn_padicIdeal_of_etale
    (A : Type u) [CommRing A] [Algebra ℤ_[p] A]
    [Algebra.Etale ℤ_[p] A] :
    Algebra.IsUnramifiedIn A (padicIdeal (p := p)) := by
  haveI : Algebra.FormallyUnramified ℤ_[p] A := inferInstance
  intro P hP _
  exact (Algebra.formallyUnramified_iff_forall.mp
    (inferInstance : Algebra.FormallyUnramified ℤ_[p] A)) ⟨P, hP⟩

/-- The fixed normalized quadratic factor is finite etale integrally. -/
theorem normalizedQuadraticModel_finiteEtale
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    Module.Finite ℤ_[p] (AdjoinRoot (normalizedQuadraticModel (p := p))) ∧
      Algebra.Etale ℤ_[p]
        (AdjoinRoot (normalizedQuadraticModel (p := p))) :=
  adjoinRoot_finiteEtale_of_monic_isCoprime
    (normalizedQuadraticModel (p := p))
    (normalizedQuadraticModel_monic hp3 hp5 hp7)
    (normalizedQuadraticModel_isCoprime_derivative hp3 hp5 hp7)

/-- The fixed normalized quartic factor is finite etale integrally. -/
theorem normalizedQuarticModel_finiteEtale
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    Module.Finite ℤ_[p] (AdjoinRoot (normalizedQuarticModel (p := p))) ∧
      Algebra.Etale ℤ_[p]
        (AdjoinRoot (normalizedQuarticModel (p := p))) :=
  adjoinRoot_finiteEtale_of_monic_isCoprime
    (normalizedQuarticModel (p := p))
    (normalizedQuarticModel_monic hp3 hp5 hp7)
    (normalizedQuarticModel_isCoprime_derivative hp3 hp5 hp7)

/-- The generic fiber of the normalized quadratic model is the existing
fixed quadratic p-adic factor. -/
def normalizedQuadraticModelGenericFiberEquiv
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (ℚ_[p] ⊗[ℤ_[p]] AdjoinRoot (normalizedQuadraticModel (p := p))) ≃ₐ[ℚ_[p]]
      QuadraticFactorAlgebra (K := ℚ_[p]) :=
  (adjoinRootBaseChangeAlgEquiv (S := ℚ_[p])
    (normalizedQuadraticModel (p := p))).trans
      (quadraticLargeFactorPadicAlgEquiv
        (normalizedQuadraticModelMonic hp3 hp5 hp7)
        hp3 hp5 hp7 rfl)

/-- The generic fiber of the normalized quartic model is the existing fixed
quartic p-adic factor. -/
def normalizedQuarticModelGenericFiberEquiv
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (ℚ_[p] ⊗[ℤ_[p]] AdjoinRoot (normalizedQuarticModel (p := p))) ≃ₐ[ℚ_[p]]
      QuarticFactorAlgebra (K := ℚ_[p]) :=
  (adjoinRootBaseChangeAlgEquiv (S := ℚ_[p])
    (normalizedQuarticModel (p := p))).trans
      (quarticLargeFactorPadicAlgEquiv
        (normalizedQuarticModelMonic hp3 hp5 hp7)
        hp3 hp5 hp7 rfl)

/-- Explicit integral product model for the `p ∣ B` branch. -/
abbrev ZeroBranchIntegralModel (b : ℤ_[p]) :=
  AdjoinRoot (normalizedQuadraticModel (p := p)) ×
    AdjoinRoot (binomialIntegralModel 5 b)

/-- Explicit integral product model for the `p ∣ A` branch. -/
abbrev OneBranchIntegralModel (b : ℤ_[p]) :=
  AdjoinRoot (normalizedQuarticModel (p := p)) ×
    AdjoinRoot (binomialIntegralModel 3 b)

private theorem not_dvd_prime_of_ne
    {q : ℕ} (hq : q.Prime) (hpq : p ≠ q) : ¬p ∣ q := by
  intro h
  exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).mp h)

/-- The zero-branch product model is finite etale. -/
theorem zeroBranchIntegralModel_finiteEtale
    (b : ℤ_[p]) (hb : IsUnit b)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    Module.Finite ℤ_[p] (ZeroBranchIntegralModel (p := p) b) ∧
      Algebra.Etale ℤ_[p] (ZeroBranchIntegralModel (p := p) b) := by
  have hlarge := normalizedQuadraticModel_finiteEtale
    (p := p) hp3 hp5 hp7
  have hsmall := binomialIntegralModel_finiteEtale b hb
    (not_dvd_prime_of_ne Nat.prime_five hp5)
  letI : Module.Finite ℤ_[p]
      (AdjoinRoot (normalizedQuadraticModel (p := p))) := hlarge.1
  letI : Module.Finite ℤ_[p]
      (AdjoinRoot (binomialIntegralModel 5 b)) := hsmall.1
  letI : Algebra.Etale ℤ_[p]
      (AdjoinRoot (normalizedQuadraticModel (p := p))) := hlarge.2
  letI : Algebra.Etale ℤ_[p]
      (AdjoinRoot (binomialIntegralModel 5 b)) := hsmall.2
  exact ⟨inferInstance, etale_prod ℤ_[p]
    (AdjoinRoot (normalizedQuadraticModel (p := p)))
    (AdjoinRoot (binomialIntegralModel 5 b))⟩

/-- The one-branch product model is finite etale. -/
theorem oneBranchIntegralModel_finiteEtale
    (b : ℤ_[p]) (hb : IsUnit b)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    Module.Finite ℤ_[p] (OneBranchIntegralModel (p := p) b) ∧
      Algebra.Etale ℤ_[p] (OneBranchIntegralModel (p := p) b) := by
  have hlarge := normalizedQuarticModel_finiteEtale
    (p := p) hp3 hp5 hp7
  have hsmall := binomialIntegralModel_finiteEtale b hb
    (not_dvd_prime_of_ne Nat.prime_three hp3)
  letI : Module.Finite ℤ_[p]
      (AdjoinRoot (normalizedQuarticModel (p := p))) := hlarge.1
  letI : Module.Finite ℤ_[p]
      (AdjoinRoot (binomialIntegralModel 3 b)) := hsmall.1
  letI : Algebra.Etale ℤ_[p]
      (AdjoinRoot (normalizedQuarticModel (p := p))) := hlarge.2
  letI : Algebra.Etale ℤ_[p]
      (AdjoinRoot (binomialIntegralModel 3 b)) := hsmall.2
  exact ⟨inferInstance, etale_prod ℤ_[p]
    (AdjoinRoot (normalizedQuarticModel (p := p)))
    (AdjoinRoot (binomialIntegralModel 3 b))⟩

/-- The zero-branch product model is unramified above the p-adic maximal
ideal. -/
theorem zeroBranchIntegralModel_isUnramifiedIn_padicIdeal
    (b : ℤ_[p]) (hb : IsUnit b)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    Algebra.IsUnramifiedIn (ZeroBranchIntegralModel (p := p) b)
      (padicIdeal (p := p)) := by
  letI : Algebra.Etale ℤ_[p] (ZeroBranchIntegralModel (p := p) b) :=
    (zeroBranchIntegralModel_finiteEtale b hb hp3 hp5 hp7).2
  exact isUnramifiedIn_padicIdeal_of_etale
    (ZeroBranchIntegralModel (p := p) b)

/-- The one-branch product model is unramified above the p-adic maximal
ideal. -/
theorem oneBranchIntegralModel_isUnramifiedIn_padicIdeal
    (b : ℤ_[p]) (hb : IsUnit b)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    Algebra.IsUnramifiedIn (OneBranchIntegralModel (p := p) b)
      (padicIdeal (p := p)) := by
  letI : Algebra.Etale ℤ_[p] (OneBranchIntegralModel (p := p) b) :=
    (oneBranchIntegralModel_finiteEtale b hb hp3 hp5 hp7).2
  exact isUnramifiedIn_padicIdeal_of_etale
    (OneBranchIntegralModel (p := p) b)

/-- Base change of the zero-branch product model is exactly the existing
quadratic-by-quintic target. -/
def zeroBranchIntegralModelGenericFiberEquiv
    (b : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (ℚ_[p] ⊗[ℤ_[p]] ZeroBranchIntegralModel (p := p) b) ≃ₐ[ℚ_[p]]
      QuadraticFactorAlgebra (K := ℚ_[p]) ×
        BinomialModelAlgebra 5 (algebraMap ℤ_[p] ℚ_[p] b) :=
  (Algebra.TensorProduct.prodRight ℤ_[p] ℚ_[p] ℚ_[p]
    (AdjoinRoot (normalizedQuadraticModel (p := p)))
    (AdjoinRoot (binomialIntegralModel 5 b))).trans
      (AlgEquiv.prodCongr
        (normalizedQuadraticModelGenericFiberEquiv hp3 hp5 hp7)
        (binomialIntegralModelGenericFiberEquiv b))

/-- Base change of the one-branch product model is exactly the existing
quartic-by-cubic target. -/
def oneBranchIntegralModelGenericFiberEquiv
    (b : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (ℚ_[p] ⊗[ℤ_[p]] OneBranchIntegralModel (p := p) b) ≃ₐ[ℚ_[p]]
      QuarticFactorAlgebra (K := ℚ_[p]) ×
        BinomialModelAlgebra 3 (algebraMap ℤ_[p] ℚ_[p] b) :=
  (Algebra.TensorProduct.prodRight ℤ_[p] ℚ_[p] ℚ_[p]
    (AdjoinRoot (normalizedQuarticModel (p := p)))
    (AdjoinRoot (binomialIntegralModel 3 b))).trans
      (AlgEquiv.prodCongr
        (normalizedQuarticModelGenericFiberEquiv hp3 hp5 hp7)
        (binomialIntegralModelGenericFiberEquiv b))

/-- Integral quintic parameter at `p ∣ B`. -/
def zeroBranchIntegralParameter (C : ℕ) : ℤ_[p] :=
  (21 : ℤ_[p])⁻¹ʳ * ((C : ℤ_[p])⁻¹ʳ) ^ 2

/-- Integral cubic parameter at `p ∣ A`.  Its negative sign means the
binomial polynomial `X^3 - b` has positive constant contribution. -/
def oneBranchIntegralParameter (C : ℕ) : ℤ_[p] :=
  (35 : ℤ_[p])⁻¹ʳ * -((C : ℤ_[p])⁻¹ʳ) ^ 4

private theorem natCast_isUnit_of_not_dvd {n : ℕ} (hn : ¬p ∣ n) :
    IsUnit (n : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hn

/-- The exact quintic parameter is a p-adic unit away from `3`, `5`, and `7`
when `C` is prime to `p`. -/
theorem zeroBranchIntegralParameter_isUnit
    (C : ℕ) (hpC : ¬p ∣ C)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    IsUnit (zeroBranchIntegralParameter (p := p) C) := by
  have hCunit : IsUnit (C : ℤ_[p]) := natCast_isUnit_of_not_dvd hpC
  obtain ⟨-, h21⟩ :=
    quadraticIntegralModel_endpoints_isUnit (p := p) hp3 hp5 hp7
  have h21' : IsUnit (21 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_coeff_zero] using h21
  exact h21'.ringInverse.mul (hCunit.ringInverse.pow 2)

/-- The exact cubic parameter is a p-adic unit away from `3`, `5`, and `7`
when `C` is prime to `p`. -/
theorem oneBranchIntegralParameter_isUnit
    (C : ℕ) (hpC : ¬p ∣ C)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    IsUnit (oneBranchIntegralParameter (p := p) C) := by
  have hCunit : IsUnit (C : ℤ_[p]) := natCast_isUnit_of_not_dvd hpC
  obtain ⟨-, h35⟩ :=
    quarticIntegralModel_endpoints_isUnit (p := p) hp3 hp5 hp7
  have h35' : IsUnit (35 : ℤ_[p]) := by
    simpa only [quarticIntegralModel_coeff_zero] using h35
  exact h35'.ringInverse.mul (hCunit.ringInverse.pow 4).neg

/-- The actual `p ∣ B` completion is the generic fiber of an explicit
finite-etale product model, which is unramified above `(p)`. -/
theorem globalFiberCompletion_of_prime_dvd_B_hasFiniteEtaleProductModel
    {B C : ℕ}
    (hB : B ≠ 0) (hBC : Nat.Coprime B C) (hpB : p ∣ B)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (Module.Finite ℤ_[p]
        (ZeroBranchIntegralModel (p := p)
          (zeroBranchIntegralParameter (p := p) C)) ∧
      Algebra.Etale ℤ_[p]
        (ZeroBranchIntegralModel (p := p)
          (zeroBranchIntegralParameter (p := p) C))) ∧
    Algebra.IsUnramifiedIn
      (ZeroBranchIntegralModel (p := p)
        (zeroBranchIntegralParameter (p := p) C))
      (padicIdeal (p := p)) ∧
    Nonempty
      ((ℚ_[p] ⊗[ℚ] GlobalFiberAlgebra B C) ≃ₐ[ℚ_[p]]
        (ℚ_[p] ⊗[ℤ_[p]]
          ZeroBranchIntegralModel (p := p)
            (zeroBranchIntegralParameter (p := p) C))) := by
  have hpC : ¬p ∣ C := by
    have hpc : Nat.Coprime p C := Nat.Coprime.of_dvd_left hpB hBC
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hpc
  have hb := zeroBranchIntegralParameter_isUnit
    (p := p) C hpC hp3 hp5 hp7
  refine ⟨zeroBranchIntegralModel_finiteEtale
      (zeroBranchIntegralParameter (p := p) C) hb hp3 hp5 hp7,
    zeroBranchIntegralModel_isUnramifiedIn_padicIdeal
      (zeroBranchIntegralParameter (p := p) C) hb hp3 hp5 hp7, ?_⟩
  obtain ⟨eglobal⟩ := globalFiberCompletion_of_prime_dvd_B
    hB hBC hpB hp3 hp5 hp7
  refine ⟨?_⟩
  simpa only [zeroBranchIntegralParameter] using eglobal.trans
    (zeroBranchIntegralModelGenericFiberEquiv
      (zeroBranchIntegralParameter (p := p) C)
      hp3 hp5 hp7).symm

/-- The actual `p ∣ A` completion is the generic fiber of an explicit
finite-etale product model, which is unramified above `(p)`.  The cubic factor
is `X^3 + 1 / (35 * C^4)`. -/
theorem globalFiberCompletion_of_prime_dvd_A_hasFiniteEtaleProductModel
    {A B C : ℕ}
    (hA : A ≠ 0) (hAC : Nat.Coprime A C) (hpA : p ∣ A)
    (hEq : A ^ 3 + B ^ 5 = C ^ 7)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    (Module.Finite ℤ_[p]
        (OneBranchIntegralModel (p := p)
          (oneBranchIntegralParameter (p := p) C)) ∧
      Algebra.Etale ℤ_[p]
        (OneBranchIntegralModel (p := p)
          (oneBranchIntegralParameter (p := p) C))) ∧
    Algebra.IsUnramifiedIn
      (OneBranchIntegralModel (p := p)
        (oneBranchIntegralParameter (p := p) C))
      (padicIdeal (p := p)) ∧
    Nonempty
      ((ℚ_[p] ⊗[ℚ] GlobalFiberAlgebra B C) ≃ₐ[ℚ_[p]]
        (ℚ_[p] ⊗[ℤ_[p]]
          OneBranchIntegralModel (p := p)
            (oneBranchIntegralParameter (p := p) C))) := by
  have hpC : ¬p ∣ C := by
    have hpc : Nat.Coprime p C := Nat.Coprime.of_dvd_left hpA hAC
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hpc
  have hb := oneBranchIntegralParameter_isUnit
    (p := p) C hpC hp3 hp5 hp7
  refine ⟨oneBranchIntegralModel_finiteEtale
      (oneBranchIntegralParameter (p := p) C) hb hp3 hp5 hp7,
    oneBranchIntegralModel_isUnramifiedIn_padicIdeal
      (oneBranchIntegralParameter (p := p) C) hb hp3 hp5 hp7, ?_⟩
  obtain ⟨eglobal⟩ := globalFiberCompletion_of_prime_dvd_A
    hA hAC hpA hEq hp3 hp5 hp7
  refine ⟨?_⟩
  simpa only [oneBranchIntegralParameter] using eglobal.trans
    (oneBranchIntegralModelGenericFiberEquiv
      (oneBranchIntegralParameter (p := p) C)
      hp3 hp5 hp7).symm

end

end BealRegular.Signature357CriticalProductFiniteEtale
