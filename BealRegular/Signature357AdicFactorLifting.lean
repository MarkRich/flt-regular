import BealRegular.Signature357PadicModelUnits
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Adic coprime factor lifting for the signature `(3,5,7)` local program

This module derives a generic Hensel-style factor-lifting theorem from
Mathlib's universal coprime factorization ring and formal smoothness.  A monic
factorization into coprime monic factors modulo an ideal lifts to an exact
coprime monic factorization over every ring complete for that ideal.  After
base change to any field algebra, the Chinese remainder theorem decomposes the
quotient algebra by the lifted product.

The constant-coefficient lemma supplies the residual coprimality pattern used
by the critical `psi * X^5` and `Psi * X^3` models.  This module does not yet
package those models as `MonicDegreeEq` data, identify either lifted factor
with an exact Dahmen--Siksek model algebra, prove structural stability or a
Newton-polygon theorem, classify valuation-theoretic ramification, exclude
signature `(3,5,7)`, or prove Beal.
-/

namespace BealRegular.Signature357AdicFactorLifting

open Polynomial

noncomputable section

universe u v

/-- A unit constant coefficient makes a polynomial coprime to every power of
`X`. -/
theorem isCoprime_X_pow_of_coeff_zero_isUnit
    {R : Type u} [CommRing R] (f : R[X])
    (hf : IsUnit (f.coeff 0)) (n : ℕ) :
    IsCoprime f (X ^ n) := by
  apply IsCoprime.pow_right
  obtain ⟨u, hu⟩ := hf
  refine ⟨C ((↑(u⁻¹) : R)), -(C ((↑(u⁻¹) : R)) * divX f), ?_⟩
  have hsplit := X_mul_divX_add f
  rw [← hu] at hsplit
  calc
    C ((↑(u⁻¹) : R)) * f + -(C ((↑(u⁻¹) : R)) * divX f) * X =
        C ((↑(u⁻¹) : R)) * (X * divX f + C (↑u)) -
          C ((↑(u⁻¹) : R)) * divX f * X := by
      rw [hsplit, sub_eq_add_neg, neg_mul]
    _ = 1 := by
      rw [mul_add, ← C_mul]
      simp only [Units.inv_mul, map_one]
      ring

/-- Once an exact coprime factorization is known over a field, CRT decomposes
the quotient algebra by the product. -/
def adjoinRootEquivProdOfCoprimeFactorization
    {K : Type v} [Field K] {p f g : K[X]}
    (hfac : p = f * g) (hcoprime : IsCoprime f g) :
    AdjoinRoot p ≃ₐ[K] AdjoinRoot f × AdjoinRoot g := by
  have hideals : IsCoprime (Ideal.span {f}) (Ideal.span {g}) :=
    (Ideal.isCoprime_span_singleton_iff f g).mpr hcoprime
  have hspan : Ideal.span {p} = Ideal.span {f} * Ideal.span {g} := by
    rw [hfac, Ideal.span_singleton_mul_span_singleton]
  exact (Ideal.quotientEquivAlgOfEq K hspan).trans <|
    AlgEquiv.ofRingEquiv
      (f := Ideal.quotientMulEquivQuotientProd _ _ hideals) (fun _ => rfl)

variable {R : Type u} [CommRing R]

/-- A coprime monic factorization modulo an ideal lifts over an adically
complete ring. -/
theorem exists_coprime_monic_factorization_of_isAdicComplete
    (I : Ideal R) [IsAdicComplete I R]
    {n m k : ℕ} (hn : n = m + k)
    (p : MonicDegreeEq R n)
    (f₀ : MonicDegreeEq (R ⧸ I) m)
    (g₀ : MonicDegreeEq (R ⧸ I) k)
    (hfac₀ : f₀.1 * g₀.1 = p.1.map (Ideal.Quotient.mk I))
    (hcoprime₀ : IsCoprime f₀.1 g₀.1) :
    ∃ (f : MonicDegreeEq R m) (g : MonicDegreeEq R k),
      f.1 * g.1 = p.1 ∧ IsCoprime f.1 g.1 ∧
      f.map (Ideal.Quotient.mk I) = f₀ ∧
      g.map (Ideal.Quotient.mk I) = g₀ := by
  let U := UniversalCoprimeFactorizationRing m k hn p
  let φ₀ : U →ₐ[R] R ⧸ I :=
    (UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I) m k hn p).symm
      ⟨(f₀, g₀), hfac₀, hcoprime₀⟩
  obtain ⟨φ, hφ⟩ :=
    Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete φ₀
  let q := UniversalCoprimeFactorizationRing.homEquiv R m k hn p φ
  refine ⟨q.1.1, q.1.2, ?_, q.2.2, ?_, ?_⟩
  · simpa using q.2.1
  · have hfmap :=
      UniversalCoprimeFactorizationRing.homEquiv_comp_fst R m k hn p φ
        (Ideal.Quotient.mkₐ R I)
    have hq₀ :
        (UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I) m k hn p φ₀).1.1 = f₀ := by
      simp [φ₀]
    rw [hφ, hq₀] at hfmap
    exact hfmap.symm
  · have hgmap :=
      UniversalCoprimeFactorizationRing.homEquiv_comp_snd R m k hn p φ
        (Ideal.Quotient.mkₐ R I)
    have hq₀ :
        (UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I) m k hn p φ₀).1.2 = g₀ := by
      simp [φ₀]
    rw [hφ, hq₀] at hgmap
    exact hgmap.symm

/-- Factor lifting followed by scalar extension to any field algebra gives an
exact CRT decomposition of the base-changed quotient. -/
theorem exists_factorization_and_fieldBaseChangeDecomposition
    (I : Ideal R) [IsAdicComplete I R]
    {K : Type v} [Field K] [Algebra R K]
    {n m k : ℕ} (hn : n = m + k)
    (p : MonicDegreeEq R n)
    (f₀ : MonicDegreeEq (R ⧸ I) m)
    (g₀ : MonicDegreeEq (R ⧸ I) k)
    (hfac₀ : f₀.1 * g₀.1 = p.1.map (Ideal.Quotient.mk I))
    (hcoprime₀ : IsCoprime f₀.1 g₀.1) :
    ∃ (f : MonicDegreeEq R m) (g : MonicDegreeEq R k),
      f.1 * g.1 = p.1 ∧ IsCoprime f.1 g.1 ∧
      f.map (Ideal.Quotient.mk I) = f₀ ∧
      g.map (Ideal.Quotient.mk I) = g₀ ∧
      Nonempty
        (AdjoinRoot (p.1.map (algebraMap R K)) ≃ₐ[K]
          AdjoinRoot (f.1.map (algebraMap R K)) ×
            AdjoinRoot (g.1.map (algebraMap R K))) := by
  obtain ⟨f, g, hfac, hcoprime, hf₀, hg₀⟩ :=
    exists_coprime_monic_factorization_of_isAdicComplete
      I hn p f₀ g₀ hfac₀ hcoprime₀
  refine ⟨f, g, hfac, hcoprime, hf₀, hg₀, ⟨?_⟩⟩
  apply adjoinRootEquivProdOfCoprimeFactorization
  · simpa [Polynomial.map_mul] using
      congrArg (Polynomial.map (algebraMap R K)) hfac.symm
  · exact hcoprime.map (Polynomial.mapRingHom (algebraMap R K))

/-- The p-adic integers satisfy the completeness hypothesis required for
factor lifting at their principal ideal generated by `p`. -/
theorem padicInt_span_p_isAdicComplete {p : ℕ} [Fact p.Prime] :
    IsAdicComplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
  rw [← PadicInt.maximalIdeal_eq_span_p]
  infer_instance

end

end BealRegular.Signature357AdicFactorLifting
