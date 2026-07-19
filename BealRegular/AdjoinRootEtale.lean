import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Finite-etale criteria for adjoin-root algebras

This module turns elementary polynomial criteria into formal and finite
etaleness of an adjoin-root algebra over an arbitrary commutative ring.  For a
monic polynomial, coprimality with its derivative gives a standard-etale
presentation.  Unit-resultant and unit-discriminant criteria then provide
convenient arithmetic corollaries, including the degree-zero case.

For the signature `(3,5,7)` program, the unit-discriminant endpoint is the
missing formal-etaleness input for applying adic rigidity to the normalized
quadratic, quartic, and separable binomial model factors.  This module does not
prove any particular discriminant is a unit, construct a residual quotient
equivalence, apply adic rigidity, identify a Dahmen--Siksek model algebra,
rescale a small factor, classify ramification, exclude signature `(3,5,7)`, or
prove Beal's conjecture.
-/

namespace BealRegular.AdjoinRootEtale

open Polynomial

noncomputable section

universe u

variable {R : Type u} [CommRing R]

private def standardEtalePairOfMonicCoprime (f : R[X]) (hf : f.Monic)
    (hcop : IsCoprime f f.derivative) : StandardEtalePair R where
  f := f
  monic_f := hf
  g := 1
  cond := by
    obtain ⟨a, b, hab⟩ := hcop
    exact ⟨b, a, 1, by simpa [mul_comm, add_comm] using hab⟩

private def standardEtaleEquivAdjoinRoot (f : R[X]) (hf : f.Monic)
    (hcop : IsCoprime f f.derivative) :
    (standardEtalePairOfMonicCoprime f hf hcop).Ring ≃ₐ[R] AdjoinRoot f :=
  (standardEtalePairOfMonicCoprime f hf hcop).equivAwayAdjoinRoot |>.trans <|
    (IsLocalization.atUnit
      (AdjoinRoot f)
      (Localization.Away (AdjoinRoot.mk f 1))
      (AdjoinRoot.mk f 1) (by simp)).symm.restrictScalars R

/-- A monic polynomial coprime to its derivative defines a formally-etale
adjoin-root algebra over any commutative ring. -/
theorem adjoinRoot_formallyEtale_of_monic_isCoprime (f : R[X]) (hf : f.Monic)
    (hcop : IsCoprime f f.derivative) :
    Algebra.FormallyEtale R (AdjoinRoot f) := by
  let P := standardEtalePairOfMonicCoprime f hf hcop
  let e : P.Ring ≃ₐ[R] AdjoinRoot f := standardEtaleEquivAdjoinRoot f hf hcop
  haveI : Algebra.FormallyEtale R P.Ring := inferInstance
  exact Algebra.FormallyEtale.of_equiv e

/-- The same hypotheses give an etale algebra. -/
theorem adjoinRoot_etale_of_monic_isCoprime (f : R[X]) (hf : f.Monic)
    (hcop : IsCoprime f f.derivative) :
    Algebra.Etale R (AdjoinRoot f) := by
  let P := standardEtalePairOfMonicCoprime f hf hcop
  let e : P.Ring ≃ₐ[R] AdjoinRoot f := standardEtaleEquivAdjoinRoot f hf hcop
  haveI : Algebra.Etale R P.Ring := inferInstance
  exact Algebra.Etale.of_equiv e

/-- The resulting etale algebra is module-finite because the defining
polynomial is monic. -/
theorem adjoinRoot_finiteEtale_of_monic_isCoprime (f : R[X]) (hf : f.Monic)
    (hcop : IsCoprime f f.derivative) :
    Module.Finite R (AdjoinRoot f) ∧ Algebra.Etale R (AdjoinRoot f) :=
  ⟨hf.finite_adjoinRoot, adjoinRoot_etale_of_monic_isCoprime f hf hcop⟩

/-- A unit resultant is an equivalent input for monic polynomials. -/
theorem adjoinRoot_finiteEtale_of_resultant_isUnit (f : R[X]) (hf : f.Monic)
    (hres : IsUnit (resultant f f.derivative)) :
    Module.Finite R (AdjoinRoot f) ∧ Algebra.Etale R (AdjoinRoot f) :=
  adjoinRoot_finiteEtale_of_monic_isCoprime f hf
    ((isUnit_resultant_iff_isCoprime hf).mp hres)

private theorem adjoinRoot_finiteEtale_of_discr_isUnit_of_degree_pos
    (f : R[X]) (hf : f.Monic)
    (hdeg : 0 < f.degree) (hdisc : IsUnit f.discr) :
    Module.Finite R (AdjoinRoot f) ∧ Algebra.Etale R (AdjoinRoot f) := by
  apply adjoinRoot_finiteEtale_of_resultant_isUnit f hf
  have hle : f.derivative.natDegree ≤ f.natDegree - 1 := natDegree_derivative_le f
  have hsum :
      f.derivative.natDegree + ((f.natDegree - 1) - f.derivative.natDegree) =
        f.natDegree - 1 := by omega
  have hres_eq :
      resultant f f.derivative f.natDegree (f.natDegree - 1) =
        resultant f f.derivative := by
    rw [← hsum, resultant_add_right_deg _ _ _ _ _ le_rfl]
    simp [hf.leadingCoeff]
  rw [← hres_eq, resultant_deriv hdeg, hf.leadingCoeff]
  simpa only [mul_one] using
    ((isUnit_one : IsUnit (1 : R)).neg.pow
      (f.natDegree * (f.natDegree - 1) / 2)).mul hdisc

/-- A monic polynomial with unit discriminant defines a finite etale
adjoin-root algebra over any commutative ring. A degree-zero monic polynomial
is `1`, so no positive-degree hypothesis is needed. -/
theorem adjoinRoot_finiteEtale_of_discr_isUnit (f : R[X]) (hf : f.Monic)
    (hdisc : IsUnit f.discr) :
    Module.Finite R (AdjoinRoot f) ∧ Algebra.Etale R (AdjoinRoot f) := by
  by_cases hzero : f.natDegree = 0
  · apply adjoinRoot_finiteEtale_of_monic_isCoprime f hf
    rw [eq_one_of_monic_natDegree_zero hf hzero]
    exact isCoprime_one_left
  · apply adjoinRoot_finiteEtale_of_discr_isUnit_of_degree_pos f hf ?_ hdisc
    rw [← natDegree_pos_iff_degree_pos]
    exact Nat.pos_of_ne_zero hzero

end

end BealRegular.AdjoinRootEtale
