import BealRegular.Signature357PolynomialBridge
import Mathlib.FieldTheory.Perfect
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Characteristic-zero base change for the `(3,5,7)` local polynomial

This module proves the Dahmen--Siksek discriminant identity over an arbitrary
characteristic-zero field.  It links the generic family directly to the
canonical rational polynomial in `Signature357PolynomialBridge`, and therefore
applies to every p-adic field `ℚ_[p]`.  It does not classify quotient algebras.
-/

namespace BealRegular.Signature357GenericLocalPolynomial

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The Dahmen--Siksek polynomial after scalar extension to `K`. -/
def phiK : K[X] :=
  15 * X ^ 7 - 35 * X ^ 6 + 21 * X ^ 5

/-- The fiber at an arbitrary parameter of the characteristic-zero field `K`. -/
def fiberK (u : K) : K[X] :=
  phiK - C u

theorem fiberK_natDegree (u : K) :
    (fiberK u).natDegree = 7 := by
  simp only [fiberK, phiK]
  compute_degree!

omit [CharZero K] in
theorem fiberK_derivative (u : K) :
    (fiberK u).derivative = 105 * (X ^ 4 * (X - C 1) ^ 2) := by
  simp [fiberK, phiK]
  simp only [C_ofNat]
  ring

private theorem fiberK_derivative_natDegree (u : K) :
    (fiberK u).derivative.natDegree = 6 := by
  rw [fiberK_derivative]
  compute_degree!

private theorem fiberK_leadingCoeff (u : K) :
    (fiberK u).leadingCoeff = 15 := by
  rw [leadingCoeff, fiberK_natDegree]
  simp [fiberK, phiK]

omit [CharZero K] in
private theorem fiberK_coeff_zero (u : K) :
    (fiberK u).coeff 0 = -u := by
  simp [fiberK, phiK]

omit [CharZero K] in
private theorem fiberK_eval_one (u : K) :
    (fiberK u).eval 1 = 1 - u := by
  simp [fiberK, phiK]
  norm_num

theorem fiberK_resultant_derivative (u : K) :
    (fiberK u).resultant (fiberK u).derivative =
      105 ^ 7 * u ^ 4 * (u - 1) ^ 2 := by
  rw [show (fiberK u).resultant (fiberK u).derivative =
      (fiberK u).resultant (fiberK u).derivative 7 6 by
    rw [fiberK_natDegree, fiberK_derivative_natDegree]]
  rw [fiberK_derivative]
  rw [show (105 : K[X]) = C 105 by rw [C_ofNat]]
  rw [resultant_C_mul_right]
  have hxdeg : ((X : K[X]) ^ 4).natDegree = 4 := by compute_degree!
  have h1powdeg : (((X : K[X]) - C 1) ^ 2).natDegree = 2 := by
    compute_degree!
  have hsplit :
      (fiberK u).resultant ((X : K[X]) ^ 4 * (X - C 1) ^ 2) 7 6 =
        (fiberK u).resultant (X ^ 4) 7 4 *
          (fiberK u).resultant ((X - C 1) ^ 2) 7 2 := by
    have h := resultant_mul_right
      (fiberK u) ((X : K[X]) ^ 4) ((X - C 1) ^ 2) 7
      (by rw [fiberK_natDegree])
    rw [hxdeg, h1powdeg] at h
    norm_num at h
    exact h
  rw [hsplit]
  have hxres : (fiberK u).resultant ((X : K[X]) ^ 4) 7 4 = u ^ 4 := by
    rw [resultant_X_pow_right (fiberK u) 7 4 (by rw [fiberK_natDegree])]
    rw [fiberK_coeff_zero]
    norm_num
  have h1res :
      (fiberK u).resultant (((X : K[X]) - C 1) ^ 2) 7 2 =
        (u - 1) ^ 2 := by
    rw [resultant_X_sub_C_pow_right (fiberK u) 1 7 2
      (by rw [fiberK_natDegree])]
    rw [fiberK_eval_one]
    norm_num
    ring
  rw [hxres, h1res]
  norm_num
  ring

/-- The Dahmen--Siksek Lemma 3.2 identity over any characteristic-zero field. -/
theorem fiberK_discr (u : K) :
    (fiberK u).discr =
      -(3 ^ 6 * 5 ^ 6 * 7 ^ 7 : K) * u ^ 4 * (u - 1) ^ 2 := by
  have hr := Polynomial.resultant_deriv (f := fiberK u) (by
    rw [← natDegree_pos_iff_degree_pos, fiberK_natDegree]
    norm_num)
  have hr' : (fiberK u).resultant (fiberK u).derivative =
      -15 * (fiberK u).discr := by
    rw [show (fiberK u).resultant (fiberK u).derivative =
        (fiberK u).resultant (fiberK u).derivative 7 6 by
      rw [fiberK_natDegree, fiberK_derivative_natDegree]]
    have hr7 : (fiberK u).resultant (fiberK u).derivative 7 6 =
        (-1) ^ (7 * 6 / 2) * 15 * (fiberK u).discr := by
      simpa only [fiberK_natDegree, Nat.reduceSub, fiberK_leadingCoeff] using hr
    rw [hr7]
    norm_num
  have hres := fiberK_resultant_derivative u
  apply (mul_left_cancel₀ (show (-15 : K) ≠ 0 by norm_num))
  rw [← hr', hres]
  ring

/-- Noncritical parameters give nonzero discriminant over every
characteristic-zero field. -/
theorem fiberK_discr_ne_zero {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    (fiberK u).discr ≠ 0 := by
  rw [fiberK_discr]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (pow_ne_zero 4 hu0))
    (pow_ne_zero 2 (sub_ne_zero.mpr hu1))

/-- The rational specialization is the canonical polynomial family already
formalized in `Signature357PolynomialBridge`. -/
theorem fiberK_rat_eq (u : ℚ) :
    fiberK (K := ℚ) u = Signature357PolynomialBridge.phi - C u := by
  simp [fiberK, phiK, Signature357PolynomialBridge.phi]
  simp only [C_ofNat]

section RationalBaseChange

variable [Algebra ℚ K]

omit [CharZero K] in
/-- The generic polynomial is scalar extension of the canonical rational
polynomial. -/
theorem phiK_eq_polynomialBridge_map :
    phiK (K := K) =
      Signature357PolynomialBridge.phi.map (algebraMap ℚ K) := by
  simp [phiK, Signature357PolynomialBridge.phi]
  simp only [C_ofNat]

omit [CharZero K] in
/-- The generic fiber is scalar extension of the canonical rational fiber. -/
theorem fiberK_algebraMap_rat (u : ℚ) :
    fiberK (algebraMap ℚ K u) =
      (Signature357PolynomialBridge.phi - C u).map (algebraMap ℚ K) := by
  simp [fiberK, phiK, Signature357PolynomialBridge.phi]
  simp only [C_ofNat]

/-- For this family, polynomial discriminant commutes with rational scalar
extension.  Mathlib currently has `resultant_map_map`, but no public general
`Polynomial.discr_map` theorem, so this follows from the two proved formulas. -/
theorem fiberK_discr_algebraMap_rat (u : ℚ) :
    (fiberK (algebraMap ℚ K u)).discr =
      algebraMap ℚ K ((Signature357PolynomialBridge.phi - C u).discr) := by
  rw [fiberK_discr, Signature357PolynomialBridge.discr_phi_sub_C]
  push_cast
  norm_num

end RationalBaseChange

/-- A noncritical fiber is separable.  This is a polynomial statement only;
it does not classify the quotient algebra or its ramification. -/
theorem fiberK_separable {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    (fiberK u).Separable := by
  rw [Polynomial.separable_def]
  by_contra hCoprime
  have hZero : (fiberK u).resultant (fiberK u).derivative = 0 :=
    Polynomial.resultant_eq_zero_iff.mpr
      ⟨Or.inl (by
        intro hFiber
        have hdegree := congrArg Polynomial.natDegree hFiber
        rw [fiberK_natDegree] at hdegree
        norm_num at hdegree), hCoprime⟩
  have hResultant := fiberK_resultant_derivative u
  rw [hZero] at hResultant
  have hRhs : (105 ^ 7 * u ^ 4 * (u - 1) ^ 2 : K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hu0))
      (pow_ne_zero 2 (sub_ne_zero.mpr hu1))
  exact hRhs hResultant.symm

/-- Equivalently, a noncritical fiber is squarefree over a characteristic-zero
field. -/
theorem fiberK_squarefree {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    Squarefree (fiberK u) :=
  PerfectField.separable_iff_squarefree.mp (fiberK_separable hu0 hu1)

/-- Polynomial separability survives every scalar extension. -/
theorem fiberK_separable_map {L : Type*} [Field L]
    (F : K →+* L) {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    ((fiberK u).map F).Separable :=
  (fiberK_separable hu0 hu1).map

omit [CharZero K] in
/-- Mapping coefficients sends a fiber to the fiber at the mapped parameter. -/
theorem fiberK_map {L : Type*} [Field L] (F : K →+* L) (u : K) :
    (fiberK u).map F = fiberK (K := L) (F u) := by
  simp [fiberK, phiK]

/-- Thus the fiber at the mapped parameter is separable after every field
extension. -/
theorem fiberK_separable_baseChange {L : Type*} [Field L]
    (F : K →+* L) {u : K} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    (fiberK (K := L) (F u)).Separable := by
  rw [← fiberK_map F u]
  exact fiberK_separable_map F hu0 hu1

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- The discriminant formula in the actual local field used by the paper. -/
theorem padicFiber_discr (u : ℚ_[p]) :
    (fiberK u).discr =
      -(3 ^ 6 * 5 ^ 6 * 7 ^ 7 : ℚ_[p]) * u ^ 4 * (u - 1) ^ 2 :=
  fiberK_discr u

/-- Every noncritical p-adic fiber is a separable polynomial. -/
theorem padicFiber_separable {u : ℚ_[p]} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    (fiberK u).Separable :=
  fiberK_separable hu0 hu1

end Padic

end


end BealRegular.Signature357GenericLocalPolynomial
