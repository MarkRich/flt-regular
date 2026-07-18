import BealRegular.Signature357GenericLocalPolynomial
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# The finite etale algebra of a noncritical `(3,5,7)` fiber

This module packages the quotient by the Dahmen--Siksek fiber polynomial.  Every
fiber has a canonical power basis of dimension seven.  At a parameter other
than zero or one, the quotient is reduced and finite etale over its coefficient
field.  The final statements specialize this construction to every p-adic
field.

Here `Algebra.Etale` is the algebraic-geometric notion over a field.  These
results do not give the valuation-theoretic unramified classification or the
product decompositions in Dahmen--Siksek Proposition 3.3.
-/

namespace BealRegular.Signature357LocalAlgebra

open Polynomial

open Signature357GenericLocalPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The canonical quotient `K[X] / (fiberK u)`. -/
abbrev FiberAlgebra (u : K) := AdjoinRoot (fiberK u)

private theorem fiberK_ne_zero (u : K) : fiberK u ≠ 0 := by
  intro hzero
  have hdegree := congrArg Polynomial.natDegree hzero
  rw [fiberK_natDegree] at hdegree
  norm_num at hdegree

/-- Every fiber quotient is finite-dimensional over its coefficient field. -/
theorem fiberAlgebra_finite (u : K) : Module.Finite K (FiberAlgebra u) :=
  (AdjoinRoot.powerBasis (fiberK_ne_zero u)).finite

omit [CharZero K] in
/-- The quotient dimension is the degree of the fiber polynomial. -/
theorem fiberAlgebra_finrank_eq_natDegree (u : K) :
    Module.finrank K (FiberAlgebra u) = (fiberK u).natDegree := by
  change Module.finrank K (K[X] ⧸ Ideal.span {fiberK u}) =
    (fiberK u).natDegree
  exact finrank_quotient_span_eq_natDegree

/-- Every fiber quotient has dimension seven. -/
theorem fiberAlgebra_finrank (u : K) :
    Module.finrank K (FiberAlgebra u) = 7 := by
  rw [fiberAlgebra_finrank_eq_natDegree, fiberK_natDegree]

/-- The canonical powers of the residue class of `X` form a power basis. -/
def fiberAlgebraPowerBasis (u : K) : PowerBasis K (FiberAlgebra u) :=
  AdjoinRoot.powerBasis (fiberK_ne_zero u)

/-- The canonical power basis has dimension seven. -/
theorem fiberAlgebraPowerBasis_dim (u : K) :
    (fiberAlgebraPowerBasis u).dim = 7 := by
  rw [fiberAlgebraPowerBasis, AdjoinRoot.powerBasis_dim, fiberK_natDegree]

/-- A noncritical fiber quotient is reduced. -/
theorem fiberAlgebra_isReduced {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    IsReduced (FiberAlgebra u) := by
  change IsReduced (K[X] ⧸ Ideal.span {fiberK u})
  rw [← Ideal.isRadical_iff_quotient_reduced]
  rw [← isRadical_iff_span_singleton]
  exact (fiberK_squarefree hu0 hu1).isRadical

/-- The monic associate used internally for the standard-etale presentation. -/
private def monicFiber (u : K) : K[X] :=
  C (15 : K)⁻¹ * fiberK u

private theorem monicFiber_associated (u : K) :
    Associated (monicFiber u) (fiberK u) := by
  apply associated_unit_mul_left
  rw [isUnit_C, isUnit_iff_ne_zero]
  exact inv_ne_zero (by norm_num)

private theorem monicFiber_monic (u : K) : (monicFiber u).Monic := by
  have hlc : (fiberK u).leadingCoeff = 15 := by
    rw [leadingCoeff, fiberK_natDegree]
    simp [fiberK, phiK]
  rw [Monic, monicFiber, leadingCoeff_mul, hlc]
  simp

private theorem monicFiber_separable {u : K}
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) : (monicFiber u).Separable :=
  (monicFiber_associated u).symm.separable (fiberK_separable hu0 hu1)

private def fiberStandardEtalePair {u : K}
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) : StandardEtalePair K where
  f := monicFiber u
  monic_f := monicFiber_monic u
  g := 1
  cond := by
    obtain ⟨a, b, hab⟩ := monicFiber_separable hu0 hu1
    exact ⟨b, a, 1, by simpa [mul_comm, add_comm] using hab⟩

private def standardEtaleEquivMonicFiber {u : K}
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    (fiberStandardEtalePair hu0 hu1).Ring ≃ₐ[K] AdjoinRoot (monicFiber u) :=
  (fiberStandardEtalePair hu0 hu1).equivAwayAdjoinRoot |>.trans <|
    ((IsLocalization.atUnit
      (AdjoinRoot (monicFiber u))
      (Localization.Away (AdjoinRoot.mk (monicFiber u) 1))
      (AdjoinRoot.mk (monicFiber u) 1) (by simp)).symm.restrictScalars K)

/-- A noncritical fiber quotient is etale over its coefficient field. -/
theorem fiberAlgebra_etale {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    Algebra.Etale K (FiberAlgebra u) := by
  let P := fiberStandardEtalePair hu0 hu1
  let e₁ : P.Ring ≃ₐ[K] AdjoinRoot (monicFiber u) :=
    standardEtaleEquivMonicFiber hu0 hu1
  let e₂ : AdjoinRoot (monicFiber u) ≃ₐ[K] FiberAlgebra u :=
    AdjoinRoot.algEquivOfAssociated K (monicFiber u) (fiberK u)
      (monicFiber_associated u)
  haveI : Algebra.Etale K P.Ring := inferInstance
  exact Algebra.Etale.of_equiv (e₁.trans e₂)

/-- A noncritical fiber quotient is finite and etale over its coefficient
field. -/
theorem fiberAlgebra_finiteEtale {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    Module.Finite K (FiberAlgebra u) ∧ Algebra.Etale K (FiberAlgebra u) :=
  ⟨fiberAlgebra_finite u, fiberAlgebra_etale hu0 hu1⟩

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- Every p-adic fiber quotient has dimension seven. -/
theorem padicFiberAlgebra_finrank (u : ℚ_[p]) :
    Module.finrank ℚ_[p] (FiberAlgebra u) = 7 :=
  fiberAlgebra_finrank u

/-- Every noncritical p-adic fiber quotient is finite etale over `Q_p`. -/
theorem padicFiberAlgebra_finiteEtale {u : ℚ_[p]}
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    Module.Finite ℚ_[p] (FiberAlgebra u) ∧
      Algebra.Etale ℚ_[p] (FiberAlgebra u) :=
  fiberAlgebra_finiteEtale hu0 hu1

end Padic

end


end BealRegular.Signature357LocalAlgebra
