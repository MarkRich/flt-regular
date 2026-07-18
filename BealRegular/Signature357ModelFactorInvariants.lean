import BealRegular.Signature357BranchNormalForms

/-!
# Model-factor invariants for signature `(3,5,7)`

This module computes exact degrees, discriminants, and separability for the
quadratic `psi`, quartic `Psi`, and normalized cubic, quintic, and septic
binomial factors used in the Dahmen--Siksek local models.

The binomial statements concern the displayed model polynomials themselves.
They do not identify an original fiber quotient with a product of model
quotients, prove structural stability or a Newton-polygon theorem, classify
valuation ramification, exclude signature `(3,5,7)`, or prove Beal.
-/

namespace BealRegular.Signature357ModelFactorInvariants

open Polynomial

open Signature357BranchNormalForms

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The quadratic factor `psiK` has degree two. -/
theorem psiK_natDegree : (psiK (K := K)).natDegree = 2 := by
  simp only [psiK]
  compute_degree!

/-- The quartic factor `PsiK` has degree four. -/
theorem PsiK_natDegree : (PsiK (K := K)).natDegree = 4 := by
  simp only [PsiK]
  compute_degree!

/-- The exact discriminant of the quadratic factor is `-35`. -/
theorem psiK_discr : (psiK (K := K)).discr = -(35 : K) := by
  have hdegree : (psiK (K := K)).degree = (2 : WithBot ℕ) := by
    have hne : psiK (K := K) ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by
      rw [psiK_natDegree]
      norm_num)
    rw [degree_eq_natDegree hne, psiK_natDegree]
    norm_num
  rw [Polynomial.discr_of_degree_eq_two hdegree]
  simp [psiK, coeff_X, coeff_X_pow]
  norm_num

omit [CharZero K] in
/-- The exact derivative of the quartic factor. -/
theorem PsiK_derivative :
    (PsiK (K := K)).derivative =
      60 * X ^ 3 + 210 * X ^ 2 + 252 * X + 105 := by
  simp [PsiK]
  simp only [C_ofNat]
  ring

/-- The exact discriminant of the quartic factor is `3^3 * 5^2 * 7^3`. -/
theorem PsiK_discr :
    (PsiK (K := K)).discr = (3 ^ 3 * 5 ^ 2 * 7 ^ 3 : K) := by
  let f : K[X] := PsiK
  have hdegree : f.natDegree = 4 := by
    exact PsiK_natDegree
  have hderivativeDegree : f.derivative.natDegree = 3 := by
    rw [Polynomial.natDegree_derivative, hdegree]
  have hleading : f.leadingCoeff = 15 := by
    rw [leadingCoeff, hdegree]
    simp [f, PsiK, coeff_X, coeff_X_pow]
  have hnormal :
      X * f.derivative =
        C (105 : K) * (X - C (-1 : K)) ^ 4 + f * C (-3 : K) := by
    simp [f, PsiK]
    simp only [C_ofNat]
    ring
  have hsplit :
      f.resultant (X * f.derivative) 4 4 =
        f.resultant X 4 1 * f.resultant f.derivative 4 3 := by
    have h := resultant_mul_right f X f.derivative 4 (by rw [hdegree])
    simpa only [natDegree_X, hderivativeDegree, Nat.reduceAdd] using h
  have hstable :
      f.resultant (X * f.derivative) 4 4 =
        f.resultant (C (105 : K) * (X - C (-1 : K)) ^ 4) 4 4 := by
    rw [hnormal]
    exact resultant_add_mul_right f
      (C (105 : K) * (X - C (-1 : K)) ^ 4) (C (-3 : K)) 4 4
      (by simp) (by rw [hdegree])
  have hscaled :
      f.resultant (C (105 : K) * (X - C (-1 : K)) ^ 4) 4 4 =
        (105 : K) ^ 4 := by
    rw [resultant_C_mul_right]
    rw [resultant_X_sub_C_pow_right f (-1 : K) 4 4 (by rw [hdegree])]
    norm_num [f, PsiK]
  have hx : f.resultant X 4 1 = (35 : K) := by
    have h := resultant_X_pow_right f 4 1 (by rw [hdegree])
    rw [pow_one] at h
    rw [h]
    norm_num [f, PsiK, coeff_X, coeff_X_pow]
  have hproduct :
      (35 : K) * f.resultant f.derivative 4 3 = (105 : K) ^ 4 := by
    rw [← hx, ← hsplit, hstable, hscaled]
  have hresultant :
      f.resultant f.derivative 4 3 =
        (15 : K) * (3 ^ 3 * 5 ^ 2 * 7 ^ 3 : K) := by
    apply (mul_left_cancel₀ (show (35 : K) ≠ 0 by norm_num))
    rw [hproduct]
    norm_num
  have hresultantDiscr :
      f.resultant f.derivative 4 3 = (15 : K) * f.discr := by
    have h := Polynomial.resultant_deriv (f := f) (by
      rw [← natDegree_pos_iff_degree_pos, hdegree]
      norm_num)
    simpa only [hdegree, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv,
      hleading, Even.neg_one_pow (by decide : Even 6), one_mul] using h
  apply (mul_left_cancel₀ (show (15 : K) ≠ 0 by norm_num))
  rw [← hresultantDiscr, hresultant]

/-- The exact discriminant of the normalized binomial `X^n - a`. -/
theorem discr_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : K) :
    (X ^ n - C a : K[X]).discr =
      (-1 : K) ^ (n * (n - 1) / 2) * (n : K) ^ n * (-a) ^ (n - 1) := by
  let f : K[X] := X ^ n - C a
  have hdegree : f.natDegree = n := by
    exact natDegree_X_pow_sub_C
  have hpositive : 0 < f.degree := by
    rw [show f.degree = n by simpa [f] using degree_X_pow_sub_C (R := K) hn a]
    exact_mod_cast hn
  have hleading : f.leadingCoeff = 1 := by
    exact (monic_X_pow_sub_C a hn.ne').leadingCoeff
  have hderivative : f.derivative = C (n : K) * X ^ (n - 1) := by
    simp [f, derivative_X_pow]
  have hresultant :
      f.resultant f.derivative n (n - 1) =
        (n : K) ^ n * (-a) ^ (n - 1) := by
    rw [hderivative, resultant_C_mul_right]
    rw [resultant_X_pow_right f n (n - 1) (by rw [hdegree])]
    have heven : Even (n * (n - 1)) := Nat.even_mul_pred_self n
    rw [heven.neg_one_pow]
    simp [f, coeff_X_pow, hn.ne'.symm]
  have hresultantDiscr :
      f.resultant f.derivative n (n - 1) =
        (-1 : K) ^ (n * (n - 1) / 2) * f.discr := by
    simpa only [hdegree, hleading, mul_one] using
      (Polynomial.resultant_deriv (f := f) hpositive)
  let s : K := (-1 : K) ^ (n * (n - 1) / 2)
  apply (mul_left_cancel₀ (show s ≠ 0 by simp [s]))
  rw [show s * f.discr = f.resultant f.derivative n (n - 1) by
    simpa only [s] using hresultantDiscr.symm]
  rw [hresultant]
  rw [show (-1 : K) ^ (n * (n - 1) / 2) = s by rfl]
  have hsquare : s * s = 1 := by
    simp [s, ← pow_add, ← two_mul, pow_mul]
  rw [show s * (s * (n : K) ^ n * (-a) ^ (n - 1)) =
      (s * s) * ((n : K) ^ n * (-a) ^ (n - 1)) by ring]
  rw [hsquare, one_mul]

/-- The exact discriminant of the normalized cubic model. -/
theorem cubicModel_discr (a : K) :
    (X ^ 3 - C a : K[X]).discr = -(3 ^ 3 : K) * a ^ 2 := by
  rw [discr_X_pow_sub_C (by norm_num : 0 < 3)]
  norm_num

/-- The exact discriminant of the normalized quintic model. -/
theorem quinticModel_discr (a : K) :
    (X ^ 5 - C a : K[X]).discr = (5 ^ 5 : K) * a ^ 4 := by
  rw [discr_X_pow_sub_C (by norm_num : 0 < 5)]
  norm_num

/-- The exact discriminant of the normalized septic model. -/
theorem septicModel_discr (a : K) :
    (X ^ 7 - C a : K[X]).discr = -(7 ^ 7 : K) * a ^ 6 := by
  rw [discr_X_pow_sub_C (by norm_num : 0 < 7)]
  norm_num

private theorem separable_of_discr_ne_zero {f : K[X]}
    (hdegree : 0 < f.natDegree) (hdiscr : f.discr ≠ 0) : f.Separable := by
  rw [Polynomial.separable_def]
  by_contra hcoprime
  have hf : f ≠ 0 := ne_zero_of_natDegree_gt (n := 0) hdegree
  have hzeroDefault : f.resultant f.derivative = 0 :=
    Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hf, hcoprime⟩
  have hzero :
      f.resultant f.derivative f.natDegree (f.natDegree - 1) = 0 := by
    simpa only [Polynomial.natDegree_derivative] using hzeroDefault
  have hresultant := Polynomial.resultant_deriv (f := f) (by
    rw [← natDegree_pos_iff_degree_pos]
    exact hdegree)
  rw [hzero] at hresultant
  exact (mul_ne_zero
    (mul_ne_zero (by simp) (leadingCoeff_ne_zero.mpr hf)) hdiscr) hresultant.symm

/-- The quadratic factor is separable in characteristic zero. -/
theorem psiK_separable : (psiK (K := K)).Separable := by
  apply separable_of_discr_ne_zero
  · rw [psiK_natDegree]
    norm_num
  · rw [psiK_discr]
    norm_num

/-- The quartic factor is separable in characteristic zero. -/
theorem PsiK_separable : (PsiK (K := K)).Separable := by
  apply separable_of_discr_ne_zero
  · rw [PsiK_natDegree]
    norm_num
  · rw [PsiK_discr]
    norm_num

/-- A normalized cubic model with nonzero parameter is separable. -/
theorem cubicModel_separable {a : K} (ha : a ≠ 0) :
    (X ^ 3 - C a : K[X]).Separable :=
  separable_X_pow_sub_C a (by norm_num) ha

/-- A normalized quintic model with nonzero parameter is separable. -/
theorem quinticModel_separable {a : K} (ha : a ≠ 0) :
    (X ^ 5 - C a : K[X]).Separable :=
  separable_X_pow_sub_C a (by norm_num) ha

/-- A normalized septic model with nonzero parameter is separable. -/
theorem septicModel_separable {a : K} (ha : a ≠ 0) :
    (X ^ 7 - C a : K[X]).Separable :=
  separable_X_pow_sub_C a (by norm_num) ha

end

end BealRegular.Signature357ModelFactorInvariants
