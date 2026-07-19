import BealRegular.Signature357GenericLocalPolynomial

/-!
# Branch normal forms for signature `(3,5,7)`

This module proves the three polynomial identities used immediately before
Dahmen--Siksek Proposition 3.3.  They are the algebraic normal forms for the
branches where the paper's `x`, `y`, or `z` is divisible by a prime.  Under the
repository's variable map, these are respectively `B`, `A`, and `C`.

In the paper, `q = p^r` in a p-adic field.  The identities themselves hold over
every field.  They do not prove the later structural-stability, quotient-product,
Newton-polygon, or valuation-theoretic unramified claims.
-/

namespace BealRegular.Signature357BranchNormalForms

open Polynomial

open Signature357GenericLocalPolynomial

noncomputable section

variable {K : Type*} [CommRing K]

/-- The quadratic factor `psi` in equation (8) of Dahmen--Siksek. -/
def psiK : K[X] :=
  15 * X ^ 2 - 35 * X + 21

/-- The quartic factor `Psi` in equation (8) of Dahmen--Siksek. -/
def PsiK : K[X] :=
  15 * X ^ 4 + 70 * X ^ 3 + 126 * X ^ 2 + 105 * X + 35

variable {K : Type*} [Field K]

/-- The `p ∣ x` normal form before the paper applies Corollary 2.2. -/
theorem fiveBranch_normalForm (q a : K) :
    fiberK (q ^ 5 * a) = X ^ 5 * psiK - C (q ^ 5 * a) := by
  simp [fiberK, phiK, psiK]
  ring

/-- The `p ∣ y` normal form after translating the variable by one. -/
theorem threeBranch_translated_normalForm (q a : K) :
    (fiberK (1 + q ^ 3 * a)).comp (X + C 1) =
      X ^ 3 * PsiK - C (q ^ 3 * a) := by
  simp [fiberK, phiK, PsiK]
  ring

/-- The equation (9) `p ∣ z` normal form after inverse scaling and clearing
`q^7`.  The paper takes `q = p^r`, so its parameter is `q⁻⁷ * a` and its
variable is scaled by `q⁻¹`. -/
theorem sevenBranch_scaled_normalForm (q a : K) (hq : q ≠ 0) :
    C (q ^ 7) * (fiberK ((q⁻¹) ^ 7 * a)).comp (C q⁻¹ * X) =
      15 * X ^ 7 - C (35 * q) * X ^ 6 +
        C (21 * q ^ 2) * X ^ 5 - C a := by
  have h7 : (C (q ^ 7) : K[X]) * C (q⁻¹ ^ 7) = 1 := by
    rw [← C_mul, ← C_1]
    congr 1
    field_simp [hq]
  have h6 : (C (q ^ 7) : K[X]) * C (q⁻¹ ^ 6) = C q := by
    rw [← C_mul]
    congr 1
    field_simp [hq]
  have h5 : (C (q ^ 7) : K[X]) * C (q⁻¹ ^ 5) = C (q ^ 2) := by
    rw [← C_mul]
    congr 1
    field_simp [hq]
  have ha : (C (q ^ 7) : K[X]) * C ((q ^ 7)⁻¹ * a) = C a := by
    rw [← C_mul]
    congr 1
    field_simp [hq]
  simp only [map_pow, fiberK, phiK, inv_pow, map_mul, sub_comp, add_comp,
    mul_comp, ofNat_comp, Nat.cast_ofNat, pow_comp, X_comp, mul_pow, C_comp]
  simp only [← C_pow, ← C_mul]
  calc
    _ = 15 * (C (q ^ 7) * C (q⁻¹ ^ 7)) * X ^ 7 -
        35 * (C (q ^ 7) * C (q⁻¹ ^ 6)) * X ^ 6 +
        21 * (C (q ^ 7) * C (q⁻¹ ^ 5)) * X ^ 5 -
        C (q ^ 7) * C ((q ^ 7)⁻¹ * a) := by ring
    _ = _ := by
      rw [h7, h6, h5, ha]
      simp only [← C_ofNat, ← C_mul]
      ring

end


end BealRegular.Signature357BranchNormalForms
