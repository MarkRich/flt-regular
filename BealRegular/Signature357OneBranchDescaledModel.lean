import BealRegular.Signature357SmallBinomialRigidity
import BealRegular.Signature357SmallFactorScaling

/-!
# The descaled cubic model in the translated-one branch

For an exact signature `(3,5,7)` factorization at `u = 1 + q ^ 3 * a`, this
module identifies the reduction of the integrally descaled degree-three factor
with `X ^ 3 - 35⁻¹ a`.  When `a` is a p-adic unit, generic binomial rigidity
then identifies the original scaled cubic adjoin-root algebra over `ℚ_[p]`
with the corresponding fixed binomial model algebra.

The final equivalence is abstract: it does not preserve a distinguished root
through the rigidity step, classify ramification, exclude signature `(3,5,7)`,
or prove Beal's conjecture.
-/

namespace BealRegular.Signature357OneBranchDescaledModel

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

private theorem translatedOne_normalForm (q a : ℤ_[p]) :
    normalizedTranslatedIntegralFiber (p := p) (1 + q ^ 3 * a) =
      C ((15 : ℤ_[p])⁻¹ʳ) *
        (X ^ 3 * quarticIntegralModel - C (q ^ 3 * a)) := by
  simp [normalizedTranslatedIntegralFiber, normalizedIntegralFiber,
    integralFiber, quarticIntegralModel,
    Signature357BranchNormalForms.PsiK]
  ring_nf
  simp

/-- Cancelling the common `q ^ 3` after substituting `X ↦ qX` gives the
exact integral factorization used to identify the residual cubic. -/
theorem oneBranch_descaled_factorization_identity
    (q a : ℤ_[p]) (hq : q ≠ 0)
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (f : MonicDegreeEq ℤ_[p] 4) (g G : MonicDegreeEq ℤ_[p] 3)
    (hfac : f.1 * g.1 =
      (normalizedTranslatedIntegralFiberMonic
        (1 + q ^ 3 * a) hp3 hp5 hp7).1)
    (hscale : G.1.scaleRoots q = g.1) :
    f.1.comp (C q * X) * G.1 =
      C ((15 : ℤ_[p])⁻¹ʳ) *
        (X ^ 3 * quarticIntegralModel.comp (C q * X) - C a) := by
  have hcomp := congrArg (fun P : ℤ_[p][X] ↦ P.comp (C q * X)) hfac
  rw [mul_comp, ← hscale, scaleRoots_comp_C_mul_X] at hcomp
  have hfiberComp :
      (normalizedTranslatedIntegralFiberMonic
        (1 + q ^ 3 * a) hp3 hp5 hp7).1.comp (C q * X) =
        C (q ^ 3) *
          (C ((15 : ℤ_[p])⁻¹ʳ) *
            (X ^ 3 * quarticIntegralModel.comp (C q * X) - C a)) := by
    change
      (normalizedTranslatedIntegralFiber (p := p) (1 + q ^ 3 * a)).comp
        (C q * X) = _
    rw [translatedOne_normalForm]
    simp only [mul_comp, sub_comp, pow_comp, X_comp, C_comp]
    simp only [map_pow, map_mul]
    ring
  rw [hfiberComp] at hcomp
  apply mul_left_cancel₀ (C_ne_zero.mpr (pow_ne_zero 3 hq))
  calc
    C (q ^ 3) * (f.1.comp (C q * X) * G.1) =
        f.1.comp (C q * X) * (C (q ^ 3) * G.1) := by ring
    _ = C (q ^ 3) *
        (C ((15 : ℤ_[p])⁻¹ʳ) *
          (X ^ 3 * quarticIntegralModel.comp (C q * X) - C a)) := hcomp

/-- The constant of the quartic model converts the normalized translated-one
equation to the monic binomial `X ^ 3 - 35⁻¹ a`. -/
theorem oneBranch_binomial_scalar_identity
    (a : ℤ_[p])
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    C ((15 : ℤ_[p])⁻¹ʳ * 35) *
        binomialIntegralModel 3 ((35 : ℤ_[p])⁻¹ʳ * a) =
      C ((15 : ℤ_[p])⁻¹ʳ) * (35 * X ^ 3 - C a) := by
  obtain ⟨-, h35⟩ := quarticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h35' : IsUnit (35 : ℤ_[p]) := by
    simpa only [quarticIntegralModel_coeff_zero] using h35
  have hcancel : (35 : ℤ_[p]) * (35 : ℤ_[p])⁻¹ʳ = 1 :=
    Ring.mul_inverse_cancel _ h35'
  have hCcancel :
      (C (35 : ℤ_[p]) : ℤ_[p][X]) * C (35 : ℤ_[p])⁻¹ʳ = 1 := by
    rw [← C_mul, hcancel, C_1]
  rw [binomialIntegralModel]
  simp only [mul_sub, C_mul]
  calc
    C ((15 : ℤ_[p])⁻¹ʳ) * C 35 * X ^ 3 -
          C ((15 : ℤ_[p])⁻¹ʳ) * C 35 *
            (C (35 : ℤ_[p])⁻¹ʳ * C a) =
        C ((15 : ℤ_[p])⁻¹ʳ) * C 35 * X ^ 3 -
          C ((15 : ℤ_[p])⁻¹ʳ) *
            (C 35 * C (35 : ℤ_[p])⁻¹ʳ) * C a := by ring
    _ = C ((15 : ℤ_[p])⁻¹ʳ) * C 35 * X ^ 3 -
          C ((15 : ℤ_[p])⁻¹ʳ) * C a := by rw [hCcancel]; ring
    _ = C ((15 : ℤ_[p])⁻¹ʳ) * (35 * X ^ 3) -
          C ((15 : ℤ_[p])⁻¹ʳ) * C a := by
      congr 1
      rw [← C_ofNat]
      ring

/-- The integral descale of the translated-one cubic has exactly the residual
binomial `X ^ 3 - 35⁻¹ a`. -/
theorem oneBranch_descaled_residual_eq
    (q a : ℤ_[p]) (hq : q ≠ 0)
    (hqI : q ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (f : MonicDegreeEq ℤ_[p] 4) (g G : MonicDegreeEq ℤ_[p] 3)
    (hfac : f.1 * g.1 =
      (normalizedTranslatedIntegralFiberMonic
        (1 + q ^ 3 * a) hp3 hp5 hp7).1)
    (hred : f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      oneQuarticResidual hp3 hp5 hp7)
    (hscale : G.1.scaleRoots q = g.1) :
    G.1.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      (binomialIntegralModel 3 ((35 : ℤ_[p])⁻¹ʳ * a)).map
        (Ideal.Quotient.mk (padicIdeal (p := p))) := by
  let π : ℤ_[p] →+* padicResidueRing (p := p) :=
    Ideal.Quotient.mk (padicIdeal (p := p))
  have hq0 : π q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hqI
  have hf0unit : IsUnit (f.1.coeff 0) :=
    oneLargeFactor_coeff_zero_isUnit f hp3 hp5 hp7 hred
  have hredpoly := congrArg Subtype.val hred
  change f.1.map π = (normalizedQuarticModel (p := p)).map π at hredpoly
  have hf0bar := congrArg
    (fun P : (padicResidueRing (p := p))[X] ↦ P.coeff 0) hredpoly
  simp only [coeff_map] at hf0bar
  have hmodelCoeff :
      (normalizedQuarticModel (p := p)).coeff 0 =
        (15 : ℤ_[p])⁻¹ʳ * 35 := by
    rw [normalizedQuarticModel, coeff_C_mul,
      quarticIntegralModel_coeff_zero]
  rw [hmodelCoeff] at hf0bar
  have hfcompmap :
      (f.1.comp (C q * X)).map π = C (π (f.1.coeff 0)) := by
    rw [map_comp]
    simp [hq0, ← coeff_zero_eq_eval_zero]
  have hrhsmap :
      (C ((15 : ℤ_[p])⁻¹ʳ) *
          (X ^ 3 * quarticIntegralModel.comp (C q * X) - C a)).map π =
        C (π ((15 : ℤ_[p])⁻¹ʳ)) *
          (35 * X ^ 3 - C (π a)) := by
    simp [hq0, quarticIntegralModel,
      Signature357BranchNormalForms.PsiK]
    ring
  have hid := oneBranch_descaled_factorization_identity
    q a hq hp3 hp5 hp7 f g G hfac hscale
  have hidmap := congrArg (Polynomial.map π) hid
  rw [Polynomial.map_mul, hfcompmap, hrhsmap] at hidmap
  have hscalar := oneBranch_binomial_scalar_identity
    (p := p) a hp3 hp5 hp7
  have hscalarmap := congrArg (Polynomial.map π) hscalar
  have hmodelmap :
      C (π (f.1.coeff 0)) *
          (binomialIntegralModel 3 ((35 : ℤ_[p])⁻¹ʳ * a)).map π =
        C (π ((15 : ℤ_[p])⁻¹ʳ)) *
          (35 * X ^ 3 - C (π a)) := by
    rw [hf0bar]
    simpa using hscalarmap
  exact ((hf0unit.map π).map C).mul_left_cancel
    (hidmap.trans hmodelmap.symm)

/-- The translated-one branch has an integral cubic descale with residual
model `X ^ 3 - 35⁻¹ a`; for unit `a`, the original scaled cubic algebra over
`ℚ_[p]` is the corresponding fixed binomial model algebra. -/
theorem oneBranch_exists_descaled_cubic_and_binomial_padicEquiv
    (q a : ℤ_[p]) (ha : IsUnit a) (hq : q ≠ 0)
    (hqI : q ∈ padicIdeal (p := p))
    (hp3 : p ≠ 3) (hp5 : p ≠ 5) (hp7 : p ≠ 7)
    (f : MonicDegreeEq ℤ_[p] 4) (g : MonicDegreeEq ℤ_[p] 3)
    (hfac : f.1 * g.1 =
      (normalizedTranslatedIntegralFiberMonic
        (1 + q ^ 3 * a) hp3 hp5 hp7).1)
    (hred : f.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
      oneQuarticResidual hp3 hp5 hp7) :
    ∃ G : MonicDegreeEq ℤ_[p] 3,
      G.1.scaleRoots q = g.1 ∧
      G.1.map (Ideal.Quotient.mk (padicIdeal (p := p))) =
        (binomialIntegralModel 3 ((35 : ℤ_[p])⁻¹ʳ * a)).map
          (Ideal.Quotient.mk (padicIdeal (p := p))) ∧
      Nonempty
        (AdjoinRoot (g.1.map (algebraMap ℤ_[p] ℚ_[p])) ≃ₐ[ℚ_[p]]
          BinomialModelAlgebra 3
            (algebraMap ℤ_[p] ℚ_[p] ((35 : ℤ_[p])⁻¹ʳ * a))) := by
  obtain ⟨G, hscale⟩ := exists_oneBranch_descaled_cubic
    q a f g hp3 hp5 hp7 hfac hred
  have hres := oneBranch_descaled_residual_eq
    q a hq hqI hp3 hp5 hp7 f g G hfac hred hscale
  refine ⟨G, hscale, hres, ?_⟩
  obtain ⟨-, h35⟩ := quarticIntegralModel_endpoints_isUnit hp3 hp5 hp7
  have h35' : IsUnit (35 : ℤ_[p]) := by
    simpa only [quarticIntegralModel_coeff_zero] using h35
  have hb : IsUnit ((35 : ℤ_[p])⁻¹ʳ * a) := h35'.ringInverse.mul ha
  have hpn : ¬p ∣ 3 := by
    intro hpdiv
    exact hp3 ((Nat.prime_dvd_prime_iff_eq
      (Fact.out : p.Prime) Nat.prime_three).mp hpdiv)
  exact ⟨originalSmallFactorPadicAlgEquivOfScaleRootsEq
    g G q ((35 : ℤ_[p])⁻¹ʳ * a) hq hb hpn hscale hres⟩

end

end BealRegular.Signature357OneBranchDescaledModel
