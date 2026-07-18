import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

/-!
# The Dahmen--Siksek polynomial bridge for signature `(3,5,7)`

This module formalizes the rational specialization of the exact polynomial
from equation (5) of Dahmen--Siksek's July 2024 working paper on
`x^5 + y^3 = z^7`.  The rational identities can later be transported to
`p`-adic fields by base change; no local-algebra classification is claimed here.
-/

namespace BealRegular.Signature357PolynomialBridge

open Polynomial

/-- The polynomial `phi(t) = 15t^7 - 35t^6 + 21t^5` from Dahmen--Siksek. -/
noncomputable def phi : ℚ[X] :=
  C 15 * X ^ 7 - C 35 * X ^ 6 + C 21 * X ^ 5

/-- The factorization at the critical value `0`. -/
theorem phi_factor_zero :
    phi = X ^ 5 * (C 15 * X ^ 2 - C 35 * X + C 21) := by
  rw [phi]
  ring

/-- The factorization after translating the critical value `1` to the origin. -/
theorem phi_comp_X_add_one_sub_one :
    phi.comp (X + 1) - 1 =
      X ^ 3 *
        (C 15 * X ^ 4 + C 70 * X ^ 3 + C 126 * X ^ 2 + C 105 * X + C 35) := by
  simp [phi]
  simp only [C_ofNat]
  ring

/-- The derivative has critical points only at `0` and `1`, with multiplicities
four and two respectively. -/
theorem derivative_phi :
    phi.derivative = C 105 * X ^ 4 * (X - 1) ^ 2 := by
  simp [phi]
  simp only [C_ofNat]
  ring

/-- Evaluation form of the factorization at `0`. -/
theorem eval_phi_factor_zero (t : ℚ) :
    phi.eval t = t ^ 5 * (15 * t ^ 2 - 35 * t + 21) := by
  rw [phi]
  simp
  ring

/-- Evaluation form of the translated factorization at `1`. -/
theorem eval_phi_add_one_sub_one (t : ℚ) :
    phi.eval (t + 1) - 1 =
      t ^ 3 * (15 * t ^ 4 + 70 * t ^ 3 + 126 * t ^ 2 + 105 * t + 35) := by
  rw [phi]
  simp
  ring

/-- Subtracting a constant does not change the degree-seven leading term. -/
theorem natDegree_phi_sub_C (eta : ℚ) :
    (phi - C eta).natDegree = 7 := by
  rw [natDegree_sub_C, phi]
  compute_degree!

/-- The leading coefficient of every member of the family `phi - eta` is `15`. -/
theorem leadingCoeff_phi_sub_C (eta : ℚ) :
    (phi - C eta).leadingCoeff = 15 := by
  rw [leadingCoeff, natDegree_phi_sub_C, coeff_sub, coeff_C]
  norm_num [phi]

/-- The value at the first critical point. -/
theorem eval_zero_phi_sub_C (eta : ℚ) :
    (phi - C eta).eval 0 = -eta := by
  simp [phi]

/-- The value at the second critical point. -/
theorem eval_one_phi_sub_C (eta : ℚ) :
    (phi - C eta).eval 1 = 1 - eta := by
  simp [phi]
  ring

/-- The resultant with the derivative, computed from the two critical values. -/
theorem resultant_derivative_phi_sub_C (eta : ℚ) :
    resultant (phi - C eta) (phi - C eta).derivative 7 6 =
      105 ^ 7 * eta ^ 4 * (eta - 1) ^ 2 := by
  have hdeg : (phi - C eta).natDegree ≤ 7 := by
    rw [natDegree_phi_sub_C]
  have hXdegree : (X ^ 4 : ℚ[X]).natDegree = 4 := by
    rw [natDegree_X_pow]
  have hOneDegree : ((X - 1) ^ 2 : ℚ[X]).natDegree = 2 := by
    rw [← C_1, natDegree_pow, natDegree_X_sub_C]
  have hmul :
      resultant (phi - C eta) (X ^ 4 * (X - 1) ^ 2) 7 6 =
        resultant (phi - C eta) (X ^ 4) 7 4 *
          resultant (phi - C eta) ((X - 1) ^ 2) 7 2 := by
    have h := resultant_mul_right (phi - C eta) (X ^ 4)
      ((X - 1) ^ 2) 7 hdeg
    rw [hXdegree, hOneDegree] at h
    norm_num at h
    exact h
  have hzero :
      resultant (phi - C eta) (X ^ 4) 7 4 = eta ^ 4 := by
    rw [resultant_X_pow_right (phi - C eta) 7 4 hdeg]
    rw [coeff_zero_eq_eval_zero, eval_zero_phi_sub_C]
    change (-1 : ℚ) ^ (7 * 4) * (-eta) ^ 4 = eta ^ 4
    norm_num
  have hone :
      resultant (phi - C eta) ((X - 1) ^ 2) 7 2 =
        (eta - 1) ^ 2 := by
    rw [← C_1]
    rw [resultant_X_sub_C_pow_right (phi - C eta) 1 7 2 hdeg]
    rw [eval_one_phi_sub_C]
    change (-1 : ℚ) ^ (7 * 2) * (1 - eta) ^ 2 = (eta - 1) ^ 2
    norm_num
    ring
  rw [derivative_sub, derivative_C, sub_zero, derivative_phi,
    mul_assoc, resultant_C_mul_right, hmul, hzero, hone]
  ring

/-- Lemma 3.2 of Dahmen--Siksek. Their nonvanishing hypotheses on `eta` are
needed for separability; the polynomial identity itself holds for every `eta`. -/
theorem discr_phi_sub_C (eta : ℚ) :
    (phi - C eta).discr =
      -(3 ^ 6 * 5 ^ 6 * 7 ^ 7) * eta ^ 4 * (eta - 1) ^ 2 := by
  have hdegree : 0 < (phi - C eta).degree := by
    rw [← natDegree_pos_iff_degree_pos, natDegree_phi_sub_C]
    norm_num
  have h := resultant_deriv (f := phi - C eta) hdegree
  rw [natDegree_phi_sub_C, leadingCoeff_phi_sub_C,
    resultant_derivative_phi_sub_C] at h
  norm_num at h ⊢
  linear_combination (1 / 15 : ℚ) * h

/-- Under the paper's hypotheses `eta ≠ 0, 1`, the discriminant is nonzero. -/
theorem discr_phi_sub_C_ne_zero {eta : ℚ} (heta0 : eta ≠ 0)
    (heta1 : eta ≠ 1) : (phi - C eta).discr ≠ 0 := by
  rw [discr_phi_sub_C]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (pow_ne_zero 4 heta0))
    (pow_ne_zero 2 (sub_ne_zero.mpr heta1))

end BealRegular.Signature357PolynomialBridge
