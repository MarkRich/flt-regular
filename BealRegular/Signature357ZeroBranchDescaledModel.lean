import BealRegular.Signature357SmallBinomialRigidity
import BealRegular.Signature357SmallFactorScaling

/-!
# The descaled quintic model in the zero branch

For an exact signature `(3,5,7)` factorization at `u = q ^ 5 * a`, this
module identifies the reduction of the integrally descaled degree-five factor
with `X ^ 5 - 21⁻¹ a`.  When `a` is a p-adic unit, generic binomial rigidity
then identifies the original scaled quintic adjoin-root algebra over `ℚ_[p]`
with the corresponding fixed binomial model algebra.

The final equivalence is abstract: it does not preserve a distinguished root
through the rigidity step, classify ramification, exclude signature `(3,5,7)`,
or prove Beal's conjecture.
-/

namespace BealRegular.Signature357ZeroBranchDescaledModel

open Polynomial
open scoped Ring

open Signature357ModelFactorAlgebras
open Signature357PadicModelUnits
open Signature357ResidualMonicModels
open Signature357SmallBinomialRigidity
open Signature357SmallFactorScaling

noncomputable section

variable {p : ℕ} [Fact p.Prime]

private theorem scaleRoots_comp_C_mul_X
    {R : Type*} [CommRing R] [Nontrivial R]
    {n : ℕ} (P : MonicDegreeEq R n) (q : R) :
    (P.1.scaleRoots q).comp (C q * X) = C (q ^ n) * P.1 := by
  have h := scaleRoots_eval₂_mul (p := P.1) C X q
  simpa only [comp, MonicDegreeEq.natDegree, eval₂_C_X, map_pow] using h

/-- Cancelling the common `q ^ 5` after substituting `X ↦ qX` gives the
exact integral factorization used to identify the residual quintic. -/
theorem zeroBranch_descaled_factorization_identity
    (q a : ℤ_[p]) (hq : q ≠ 0)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (f : MonicDegreeEq ℤ_[p] 2) (g G : MonicDegreeEq ℤ_[p] 5)
    (hfac : f.1 * g.1 =
      (normalizedIntegralFiberMonic (q ^ 5 * a) hp3 hp5 hp7).1)
    (hscale : G.1.scaleRoots q = g.1) :
    f.1.comp (C q * X) * G.1 =
      C ((15 : ℤ_[p])⁻¹ʳ) *
        (15 * C (q ^ 2) * X ^ 7 - 35 * C q * X ^ 6 +
          21 * X ^ 5 - C a) := by
  have hcomp := congrArg (fun P : ℤ_[p][X] ↦ P.comp (C q * X)) hfac
  rw [mul_comp, ← hscale, scaleRoots_comp_C_mul_X] at hcomp
  have hfiberComp :
      (normalizedIntegralFiberMonic (q ^ 5 * a) hp3 hp5 hp7).1.comp
          (C q * X) =
        C (q ^ 5) *
          (C ((15 : ℤ_[p])⁻¹ʳ) *
            (15 * C (q ^ 2) * X ^ 7 - 35 * C q * X ^ 6 +
              21 * X ^ 5 - C a)) := by
    change
      (C ((15 : ℤ_[p])⁻¹ʳ) *
        (15 * X ^ 7 - 35 * X ^ 6 + 21 * X ^ 5 - C (q ^ 5 * a))).comp
          (C q * X) = _
    simp only [mul_comp, C_comp, sub_comp, add_comp, pow_comp, X_comp,
      ofNat_comp, Nat.cast_ofNat]
    simp only [map_pow, map_mul]
    ring
  rw [hfiberComp] at hcomp
  apply mul_left_cancel₀ (C_ne_zero.mpr (pow_ne_zero 5 hq))
  calc
    C (q ^ 5) * (f.1.comp (C q * X) * G.1) =
        f.1.comp (C q * X) * (C (q ^ 5) * G.1) := by ring
    _ = C (q ^ 5) *
          (C ((15 : ℤ_[p])⁻¹ʳ) *
            (15 * C (q ^ 2) * X ^ 7 - 35 * C q * X ^ 6 +
              21 * X ^ 5 - C a)) := hcomp

/-- The constant of the quadratic model converts the normalized zero-branch
equation to the monic binomial `X ^ 5 - 21⁻¹ a`. -/
theorem zeroBranch_binomial_scalar_identity
    (a : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    C ((15 : ℤ_[p])⁻¹ʳ * 21) *
        binomialIntegralModel 5 ((21 : ℤ_[p])⁻¹ʳ * a) =
      C ((15 : ℤ_[p])⁻¹ʳ) * (21 * X ^ 5 - C a) := by
  obtain ⟨-, h21⟩ := quadraticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h21' : IsUnit (21 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_coeff_zero] using h21
  have hcancel : (21 : ℤ_[p]) * (21 : ℤ_[p])⁻¹ʳ = 1 :=
    Ring.mul_inverse_cancel _ h21'
  have hCcancel :
      (C (21 : ℤ_[p]) : ℤ_[p][X]) * C (21 : ℤ_[p])⁻¹ʳ = 1 := by
    rw [← C_mul, hcancel, C_1]
  rw [binomialIntegralModel]
  simp only [mul_sub, C_mul]
  calc
    C ((15 : ℤ_[p])⁻¹ʳ) * C 21 * X ^ 5 -
          C ((15 : ℤ_[p])⁻¹ʳ) * C 21 *
            (C (21 : ℤ_[p])⁻¹ʳ * C a) =
        C ((15 : ℤ_[p])⁻¹ʳ) * C 21 * X ^ 5 -
          C ((15 : ℤ_[p])⁻¹ʳ) *
            (C 21 * C (21 : ℤ_[p])⁻¹ʳ) * C a := by ring
    _ = C ((15 : ℤ_[p])⁻¹ʳ) * C 21 * X ^ 5 -
          C ((15 : ℤ_[p])⁻¹ʳ) * C a := by rw [hCcancel]; ring
    _ = C ((15 : ℤ_[p])⁻¹ʳ) * (21 * X ^ 5) -
          C ((15 : ℤ_[p])⁻¹ʳ) * C a := by
      congr 1
      rw [← C_ofNat]
      ring

/-- The integral descale of the zero-branch quintic has exactly the residual
binomial `X ^ 5 - 21⁻¹ a`. -/
theorem zeroBranch_descaled_residual_eq
    (q a : ℤ_[p]) (hq : q ≠ 0)
    (hqI : q ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (f : MonicDegreeEq ℤ_[p] 2) (g G : MonicDegreeEq ℤ_[p] 5)
    (hfac : f.1 * g.1 =
      (normalizedIntegralFiberMonic (q ^ 5 * a) hp3 hp5 hp7).1)
    (hred : f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      zeroQuadraticResidual hp3 hp5 hp7)
    (hscale : G.1.scaleRoots q = g.1) :
    G.1.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      (binomialIntegralModel 5 ((21 : ℤ_[p])⁻¹ʳ * a)).map
        (Ideal.Quotient.mk (padicIdeal (p := p))) := by
  let π : ℤ_[p] →+* padicResidueRing (p := p) :=
    Ideal.Quotient.mk (padicIdeal (p := p))
  have hq0 : π q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hqI
  have hf0unit : IsUnit (f.1.coeff 0) :=
    zeroLargeFactor_coeff_zero_isUnit f hp3 hp5 hp7 hred
  have hredpoly := congrArg Subtype.val hred
  change f.1.map π = (normalizedQuadraticModel (p := p)).map π at hredpoly
  have hf0bar := congrArg
    (fun P : (padicResidueRing (p := p))[X] ↦ P.coeff 0) hredpoly
  simp only [coeff_map] at hf0bar
  have hmodelCoeff :
      (normalizedQuadraticModel (p := p)).coeff 0 =
        (15 : ℤ_[p])⁻¹ʳ * 21 := by
    rw [normalizedQuadraticModel, coeff_C_mul,
      quadraticIntegralModel_coeff_zero]
  rw [hmodelCoeff] at hf0bar
  have hfcompmap :
      (f.1.comp (C q * X)).map π = C (π (f.1.coeff 0)) := by
    rw [map_comp]
    simp [hq0, ← coeff_zero_eq_eval_zero]
  have hrhsmap :
      (C ((15 : ℤ_[p])⁻¹ʳ) *
          (15 * C (q ^ 2) * X ^ 7 - 35 * C q * X ^ 6 +
            21 * X ^ 5 - C a)).map π =
        C (π ((15 : ℤ_[p])⁻¹ʳ)) *
          (21 * X ^ 5 - C (π a)) := by
    simp [hq0]
  have hid := zeroBranch_descaled_factorization_identity
    q a hq hp3 hp5 hp7 f g G hfac hscale
  have hidmap := congrArg (Polynomial.map π) hid
  rw [Polynomial.map_mul, hfcompmap, hrhsmap] at hidmap
  have hscalar := zeroBranch_binomial_scalar_identity
    (p := p) a hp3 hp5 hp7
  have hscalarmap := congrArg (Polynomial.map π) hscalar
  have hmodelmap :
      C (π (f.1.coeff 0)) *
          (binomialIntegralModel 5 ((21 : ℤ_[p])⁻¹ʳ * a)).map π =
        C (π ((15 : ℤ_[p])⁻¹ʳ)) *
          (21 * X ^ 5 - C (π a)) := by
    rw [hf0bar]
    simpa using hscalarmap
  exact ((hf0unit.map π).map C).mul_left_cancel
    (hidmap.trans hmodelmap.symm)

/-- The zero branch has an integral quintic descale with residual model
`X ^ 5 - 21⁻¹ a`; for unit `a`, the original scaled quintic algebra over
`ℚ_[p]` is the corresponding fixed binomial model algebra. -/
theorem zeroBranch_exists_descaled_quintic_and_binomial_padicEquiv
    (q a : ℤ_[p]) (ha : IsUnit a) (hq : q ≠ 0)
    (hqI : q ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (f : MonicDegreeEq ℤ_[p] 2) (g : MonicDegreeEq ℤ_[p] 5)
    (hfac : f.1 * g.1 =
      (normalizedIntegralFiberMonic (q ^ 5 * a) hp3 hp5 hp7).1)
    (hred : f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      zeroQuadraticResidual hp3 hp5 hp7) :
    ∃ G : MonicDegreeEq ℤ_[p] 5,
      G.1.scaleRoots q = g.1 ∧
      G.1.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
        (binomialIntegralModel 5 ((21 : ℤ_[p])⁻¹ʳ * a)).map
          (Ideal.Quotient.mk (padicIdeal (p := p))) ∧
      Nonempty
        (AdjoinRoot (g.1.map (algebraMap ℤ_[p] ℚ_[p])) ≃ₐ[ℚ_[p]]
          BinomialModelAlgebra 5
            (algebraMap ℤ_[p] ℚ_[p] ((21 : ℤ_[p])⁻¹ʳ * a))) := by
  obtain ⟨G, hscale⟩ := exists_zeroBranch_descaled_quintic
    q a f g hp3 hp5 hp7 hfac hred
  have hres := zeroBranch_descaled_residual_eq
    q a hq hqI hp3 hp5 hp7 f g G hfac hred hscale
  refine ⟨G, hscale, hres, ?_⟩
  obtain ⟨-, h21⟩ := quadraticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h21' : IsUnit (21 : ℤ_[p]) := by
    simpa only [quadraticIntegralModel_coeff_zero] using h21
  have hb : IsUnit ((21 : ℤ_[p])⁻¹ʳ * a) := h21'.ringInverse.mul ha
  have hpn : ¬p ∣ 5 := by
    intro hpdiv
    exact hp5 ((Nat.prime_dvd_prime_iff_eq
      (Fact.out : p.Prime) Nat.prime_five).mp hpdiv)
  exact ⟨originalSmallFactorPadicAlgEquivOfScaleRootsEq
    g G q ((21 : ℤ_[p])⁻¹ʳ * a) hq hb hpn hscale hres⟩

end

end BealRegular.Signature357ZeroBranchDescaledModel
