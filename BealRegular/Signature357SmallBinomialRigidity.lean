import BealRegular.AdjoinRootBaseChange
import BealRegular.Signature357LargeFactorRigidity
import BealRegular.Signature357ModelFactorAlgebras
import BealRegular.WeightedPolynomialScaling

/-!
# Binomial rigidity for the descaled signature `(3,5,7)` small factors

This module identifies a monic polynomial over the p-adic integers with a
binomial model when their reductions agree and the binomial is separable.  It
then extends the resulting equivalence to the p-adic numbers.  Finally, an
integral `scaleRoots` identity is mapped to the p-adic numbers, where the
nonzero scale is a unit, and is composed with the binomial-model equivalence.

The last construction identifies the adjoin-root algebra of the original
scaled factor; it does not assert equality of the original and descaled
polynomials, preserve a distinguished root through the rigidity equivalence,
establish the residual binomial identity, prove a factorization, or exclude
signature `(3,5,7)`.
-/

namespace BealRegular.Signature357SmallBinomialRigidity

open Polynomial

open AdjoinRootBaseChange
open Signature357LargeFactorRigidity
open Signature357ModelFactorAlgebras
open Signature357PadicModelUnits
open Signature357ResidualMonicModels
open WeightedPolynomialScaling

noncomputable section

variable {p n : ℕ} [Fact p.Prime]

/-- The integral polynomial `X ^ n - C b`, packaged with its degree. -/
def binomialIntegralModelMonic (b : ℤ_[p]) (hpn : ¬p ∣ n) :
    MonicDegreeEq ℤ_[p] n := by
  have hn : 0 < n := Nat.pos_of_ne_zero <| by
    intro hn0
    apply hpn
    rw [hn0]
    exact dvd_zero p
  exact MonicDegreeEq.mk (binomialIntegralModel n b)
    (binomialIntegralModel_monic b hn)
    (binomialIntegralModel_natDegree n b)

/-- A unit constant term and `p ∤ n` make the integral binomial coprime to
its derivative. -/
theorem binomialIntegralModel_isCoprime_derivative
    {b : ℤ_[p]} (hb : IsUnit b) (hpn : ¬p ∣ n) :
    IsCoprime (binomialIntegralModel n b)
      (binomialIntegralModel n b).derivative := by
  have hn : 0 < n := Nat.pos_of_ne_zero <| by
    intro hn0
    apply hpn
    rw [hn0]
    exact dvd_zero p
  apply isCoprime_derivative_of_isUnit_leadingCoeff_discr
  · rw [← natDegree_pos_iff_degree_pos,
      binomialIntegralModel_natDegree]
    exact hn
  · rw [binomialIntegralModel_leadingCoeff b hn]
    exact isUnit_one
  · exact binomialIntegralModel_discr_isUnit hn hb hpn

/-- A monic integral lift of the same separable residual binomial has an
equivalent integral adjoin-root algebra. -/
def descaledSmallFactorIntegralAlgEquiv
    (G : MonicDegreeEq ℤ_[p] n) (b : ℤ_[p])
    (hb : IsUnit b) (hpn : ¬p ∣ n)
    (hred : G.1.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      (binomialIntegralModel n b).map
        (Ideal.Quotient.mk (padicIdeal (p := p)))) :
    AdjoinRoot G.1 ≃ₐ[ℤ_[p]] AdjoinRoot (binomialIntegralModel n b) :=
  let hn : 0 < n := Nat.pos_of_ne_zero <| by
    intro hn0
    apply hpn
    rw [hn0]
    exact dvd_zero p
  padicAdjoinRootAlgEquivOfMapEqIsCoprime
    G.1 (binomialIntegralModel n b) G.monic
    (binomialIntegralModel_monic b hn)
    (binomialIntegralModel_isCoprime_derivative hb hpn)
    hred

/-- Version of `descaledSmallFactorIntegralAlgEquiv` whose residual equality
is stated between degree-packaged monic polynomials. -/
def descaledSmallFactorIntegralAlgEquivOfMonicMapEq
    (G : MonicDegreeEq ℤ_[p] n) (b : ℤ_[p])
    (hb : IsUnit b) (hpn : ¬p ∣ n)
    (hred : G.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      (binomialIntegralModelMonic b hpn).map
        (Ideal.Quotient.mk (padicIdeal (p := p)))) :
    AdjoinRoot G.1 ≃ₐ[ℤ_[p]] AdjoinRoot (binomialIntegralModel n b) := by
  apply descaledSmallFactorIntegralAlgEquiv G b hb hpn
  have hredpoly := congrArg Subtype.val hred
  change G.1.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
    (binomialIntegralModel n b).map
      (Ideal.Quotient.mk (padicIdeal (p := p))) at hredpoly
  exact hredpoly

/-- After scalar extension, the descaled factor is the p-adic binomial model
algebra `ℚ_[p][X] / (X ^ n - b)`. -/
def descaledSmallFactorPadicAlgEquiv
    (G : MonicDegreeEq ℤ_[p] n) (b : ℤ_[p])
    (hb : IsUnit b) (hpn : ¬p ∣ n)
    (hred : G.1.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      (binomialIntegralModel n b).map
        (Ideal.Quotient.mk (padicIdeal (p := p)))) :
    AdjoinRoot (G.1.map (algebraMap ℤ_[p] ℚ_[p])) ≃ₐ[ℚ_[p]]
      BinomialModelAlgebra n (algebraMap ℤ_[p] ℚ_[p] b) := by
  have hmap :
      (binomialIntegralModel n b).map (algebraMap ℤ_[p] ℚ_[p]) =
        X ^ n - C (algebraMap ℤ_[p] ℚ_[p] b) := by
    simp [binomialIntegralModel]
  exact
    (adjoinRootMapAlgEquivOfAlgEquiv (S := ℚ_[p])
      (descaledSmallFactorIntegralAlgEquiv G b hb hpn hred)).trans
        (AdjoinRoot.algEquivOfEq ℚ_[p] _ _ hmap)

/-- Mapping an integral root-scaling identity to the p-adic numbers preserves
the identity. -/
theorem map_scaleRoots_eq_padic
    (g G : MonicDegreeEq ℤ_[p] n) (q : ℤ_[p])
    (hscale : G.1.scaleRoots q = g.1) :
    (G.1.map (algebraMap ℤ_[p] ℚ_[p])).scaleRoots
        (algebraMap ℤ_[p] ℚ_[p] q) =
      g.1.map (algebraMap ℤ_[p] ℚ_[p]) := by
  rw [← Polynomial.map_scaleRoots G.1 q (algebraMap ℤ_[p] ℚ_[p])]
  · rw [hscale]
  · rw [G.monic.leadingCoeff]
    simp

/-- A nonzero integral scale becomes a unit over the p-adic numbers. -/
theorem isUnit_algebraMap_padic_of_ne_zero {q : ℤ_[p]} (hq : q ≠ 0) :
    IsUnit (algebraMap ℤ_[p] ℚ_[p] q) := by
  rw [isUnit_iff_ne_zero, map_ne_zero_iff
    (algebraMap ℤ_[p] ℚ_[p]) (IsFractionRing.injective ℤ_[p] ℚ_[p])]
  exact hq

/-- If `G.scaleRoots q = g` integrally, with nonzero `q`, and `G` has the
separable binomial residual model, then the original factor algebra over the
p-adic numbers is equivalent to that binomial model algebra. -/
def originalSmallFactorPadicAlgEquivOfScaleRootsEq
    (g G : MonicDegreeEq ℤ_[p] n) (q b : ℤ_[p])
    (hq : q ≠ 0) (hb : IsUnit b) (hpn : ¬p ∣ n)
    (hscale : G.1.scaleRoots q = g.1)
    (hred : G.1.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      (binomialIntegralModel n b).map
        (Ideal.Quotient.mk (padicIdeal (p := p)))) :
    AdjoinRoot (g.1.map (algebraMap ℤ_[p] ℚ_[p])) ≃ₐ[ℚ_[p]]
      BinomialModelAlgebra n (algebraMap ℤ_[p] ℚ_[p] b) :=
  let hscaleQp := map_scaleRoots_eq_padic g G q hscale
  (AdjoinRoot.algEquivOfEq ℚ_[p] _ _ hscaleQp.symm).trans <|
    (adjoinRootScaleRootsAlgEquiv
      (G.1.map (algebraMap ℤ_[p] ℚ_[p]))
      (algebraMap ℤ_[p] ℚ_[p] q)
      (isUnit_algebraMap_padic_of_ne_zero hq)).trans <|
        descaledSmallFactorPadicAlgEquiv G b hb hpn hred

end

end BealRegular.Signature357SmallBinomialRigidity
