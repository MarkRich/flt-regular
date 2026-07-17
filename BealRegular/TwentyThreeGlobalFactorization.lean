import BealRegular.TwentyThreeDedekindLocalFactors
import BealRegular.TwentyThreeOddCharacterAnalyticBridge
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# The global odd-character factorization at 23

This file assembles the pointwise Dedekind local-factor identities at `23`
with the unconditional Dedekind-zeta and Dirichlet Euler products on
`Re(s) > 1`.  The resulting global factorization discharges the last explicit
hypothesis of `TwentyThreeOddCharacterAnalyticBridge`, yielding cyclotomic
class number `3`, regularity of `23`, and Fermat's Last Theorem for exponent
`23`.
-/

open scoped BigOperators NumberField LSeries.notation

namespace BealRegular.TwentyThreeGlobalFactorization

open DirichletCharacter NumberField
open BealRegular.DedekindZetaEulerProduct
open BealRegular.TwentyThreeDedekindLocalFactors
open BealRegular.TwentyThreeOddCharacterAnalyticBridge

noncomputable section

local notation "K23" => CyclotomicField 23 ℚ
local notation "K23plus" => NumberField.maximalRealSubfield K23

/-- The finite product of the eleven odd Dirichlet local factors. -/
def oddDirichletLocalFactor (s : ℂ) (q : Nat.Primes) : ℂ :=
  ∏ χ ∈ BealRegular.oddCharacters23,
    (1 - χ (q : ℕ) * ((q : ℕ) : ℂ) ^ (-s))⁻¹

theorem oddDirichletLocalFactor_eq_localFactorX (s : ℂ) (q : Nat.Primes) :
    oddDirichletLocalFactor s q =
      oddCharacterLocalFactorX
        ((q : ℕ) : ZMod 23) (((q : ℕ) : ℂ) ^ (-s)) := by
  rfl

/-- The local factorization holds at every rational prime. -/
theorem dedekind_local_factorization (s : ℂ) (q : Nat.Primes) :
    dedekindRationalLocalFactor K23 s q =
      dedekindRationalLocalFactor K23plus s q *
        oddDirichletLocalFactor s q := by
  rw [oddDirichletLocalFactor_eq_localFactorX]
  by_cases hq23 : (q : ℕ) = 23
  · have hqeq : q = (⟨23, by decide⟩ : Nat.Primes) := by
      apply Subtype.ext
      exact hq23
    subst q
    exact ramified_dedekind_local_factorization s
  · exact unramified_dedekind_local_factorization s q.property hq23

/-- The finite product of the eleven Dirichlet Euler products. -/
theorem oddDirichletLocalFactor_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (oddDirichletLocalFactor s)
      (∏ χ ∈ BealRegular.oddCharacters23, L ↗χ s) := by
  unfold oddDirichletLocalFactor
  apply hasProd_prod
  intro χ hχ
  exact DirichletCharacter.LSeries_eulerProduct_hasProd χ hs

/-- The unconditional global odd-character factorization on the half-plane
of absolute convergence. -/
theorem globalFactorizationTwentyThree :
    GlobalFactorizationTwentyThree := by
  intro s hs
  have hfull := dedekindZeta_rationalEulerProduct_hasProd K23 hs
  have hreal := dedekindZeta_rationalEulerProduct_hasProd K23plus hs
  have hodd := oddDirichletLocalFactor_hasProd s hs
  have hproduct : HasProd
      (fun q ↦ dedekindRationalLocalFactor K23plus s q *
        oddDirichletLocalFactor s q)
      (dedekindZeta K23plus s *
        ∏ χ ∈ BealRegular.oddCharacters23, L ↗χ s) :=
    hreal.mul hodd
  exact hfull.unique (hproduct.congr_fun (dedekind_local_factorization s))

/-- The completed cyclotomic class-number computation at `23`. -/
theorem classNumber_cyclotomicTwentyThree_eq_three :
    NumberField.classNumber K23 = 3 :=
  classNumber_eq_three_of_globalFactorization globalFactorizationTwentyThree

/-- The prime `23` is regular. -/
theorem isRegularPrime_twentyThree : IsRegularPrime 23 :=
  isRegularPrime_twentyThree_of_globalFactorization globalFactorizationTwentyThree

/-- Fermat's Last Theorem for exponent `23`. -/
theorem fermatLastTheoremTwentyThree : FermatLastTheoremFor 23 :=
  fermatLastTheoremTwentyThree_of_globalFactorization
    globalFactorizationTwentyThree

end

end BealRegular.TwentyThreeGlobalFactorization

/-! Standard global theorem names, matching the existing exponent-17 and
exponent-19 endpoints. -/

theorem isRegularPrime_twentyThree : IsRegularPrime 23 :=
  BealRegular.TwentyThreeGlobalFactorization.isRegularPrime_twentyThree

theorem fermatLastTheoremTwentyThree : FermatLastTheoremFor 23 :=
  BealRegular.TwentyThreeGlobalFactorization.fermatLastTheoremTwentyThree
