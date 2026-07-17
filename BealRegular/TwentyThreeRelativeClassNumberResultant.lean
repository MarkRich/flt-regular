module

public import BealRegular.TwentyThreeRealSubfieldDiscriminant

/-!
# The odd-character resultant at 23

The odd Dirichlet characters modulo `23` can be indexed by the roots of
`X^11 + 1` after choosing `5` as a primitive residue.  Their finite weighted
character sums are encoded by `characterSumPolynomial`.

This file checks, by an exact polynomial remainder chain over `ℚ`, that the
resultant of these two polynomials is `-3 * 46^10`.  The computation is the
finite algebraic side of the relative class-number formula; no analytic
class-number formula is asserted here.
-/

@[expose] public section

open Polynomial

namespace BealRegular.TwentyThreeRelativeClassNumberResultant

noncomputable section

private lemma C_eq_smul_one (a : ℚ) :
    C a = a • (1 : ℚ[X]) := by
  rw [← Polynomial.C_1, Polynomial.smul_C]
  simp

private lemma resultant_step
    {f g h q : ℚ[X]} {m n d : ℕ} {c : ℚ}
    (hf : f.natDegree = m)
    (hg : g.natDegree = n)
    (hh : h.natDegree = d)
    (hdm : d ≤ m)
    (hgm : g.Monic)
    (hc : c ≠ 0)
    (hq : q.natDegree + n ≤ m)
    (heq : f = C c * h + g * q) :
    f.resultant g = (-1 : ℚ) ^ (m * n) * c ^ n * g.resultant h := by
  have hch : (C c * h).natDegree = d := by
    rw [natDegree_C_mul hc, hh]
  have hgc : g.coeff n = 1 := by
    rw [← hg]
    exact hgm.coeff_natDegree
  rw [show f.resultant g = f.resultant g m n by simp [hf, hg]]
  rw [heq]
  rw [resultant_add_mul_left _ _ _ _ _ hq (by simp [hg])]
  rw [show m = d + (m - d) by omega]
  rw [resultant_add_left_deg _ _ _ _ _ hch.le]
  rw [hgc, one_pow, mul_one]
  rw [resultant_C_mul_left]
  rw [resultant_comm]
  rw [show g.resultant h n d = g.resultant h by simp [hg, hh]]
  have hsign :
      (-1 : ℚ) ^ (n * (m - d)) * (-1 : ℚ) ^ (d * n) =
        (-1 : ℚ) ^ ((d + (m - d)) * n) := by
    rw [← pow_add]
    congr 1
    rw [Nat.add_mul]
    ac_rfl
  calc
    (-1 : ℚ) ^ (n * (m - d)) *
          (c ^ n * ((-1 : ℚ) ^ (d * n) * g.resultant h)) =
        ((-1 : ℚ) ^ (n * (m - d)) * (-1 : ℚ) ^ (d * n)) *
          c ^ n * g.resultant h := by ring
    _ = (-1 : ℚ) ^ ((d + (m - d)) * n) * c ^ n * g.resultant h := by
      rw [hsign]

/-- The polynomial whose roots index the odd characters modulo `23`. -/
def oddCharacterRootPolynomial : ℚ[X] := X ^ 11 + 1

private def p10 : ℚ[X] :=
  X ^ 10 + C (1 / 5) * X ^ 9 + C (-9 / 5) * X ^ 8 +
    C (-11 / 5) * X ^ 7 + C (7 / 5) * X ^ 6 + C (-17 / 5) * X ^ 5 +
      C 3 * X ^ 4 + C (3 / 5) * X ^ 3 + C (19 / 5) * X ^ 2 +
        C (13 / 5) * X + C (21 / 5)

private def p9 : ℚ[X] :=
  X ^ 9 + X ^ 8 - X ^ 7 + C 2 * X ^ 6 - C 2 * X ^ 5 -
    C 2 * X ^ 3 - X ^ 2 - C 2 * X + 1

private def p7 : ℚ[X] :=
  X ^ 7 - X ^ 6 + X ^ 5 - X ^ 4 - X ^ 2 - 1

private def p6 : ℚ[X] := X ^ 6 + X ^ 4 + 1

private def p2 : ℚ[X] := X ^ 2 + X

private def p1 : ℚ[X] := X + C (-1 / 2)

private def p0 : ℚ[X] := 1

private lemma res11_10 :
    oddCharacterRootPolynomial.resultant p10 =
      (46 / 25 : ℚ) ^ 10 * p10.resultant p9 := by
  rw [show (46 / 25 : ℚ) ^ 10 * p10.resultant p9 =
      (-1 : ℚ) ^ (11 * 10) * (46 / 25 : ℚ) ^ 10 *
        p10.resultant p9 by norm_num]
  apply resultant_step (m := 11) (n := 10) (d := 9)
    (q := X + C (-1 / 5))
  · simp only [oddCharacterRootPolynomial]
    compute_degree!
  · simp only [p10]
    compute_degree!
  · simp only [p9]
    compute_degree!
  · norm_num
  · simp only [p10]
    monicity!
  · norm_num
  · have hq : (X + C (-1 / 5) : ℚ[X]).natDegree = 1 := by
      compute_degree!
    omega
  · simp [oddCharacterRootPolynomial, p10, p9]
    ring_nf
    simp only [← Polynomial.C_mul]
    norm_num
    simp only [C_eq_smul_one]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [one_mul, mul_one]
    module

private lemma res10_9 :
    p10.resultant p9 = (-5 : ℚ) ^ 9 * p9.resultant p7 := by
  rw [show (-5 : ℚ) ^ 9 * p9.resultant p7 =
      (-1 : ℚ) ^ (10 * 9) * (-5 : ℚ) ^ 9 * p9.resultant p7 by
        norm_num]
  apply resultant_step (m := 10) (n := 9) (d := 7)
    (q := X + C (-4 / 5))
  · simp only [p10]
    compute_degree!
  · simp only [p9]
    compute_degree!
  · simp only [p7]
    compute_degree!
  · norm_num
  · simp only [p9]
    monicity!
  · norm_num
  · have hq : (X + C (-4 / 5) : ℚ[X]).natDegree = 1 := by
      compute_degree!
    omega
  · simp [p10, p9, p7]
    ring_nf
    norm_num
    simp only [C_eq_smul_one]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [one_mul, mul_one]
    module

private lemma res9_7 :
    p9.resultant p7 = (-1 : ℚ) * p7.resultant p6 := by
  rw [show (-1 : ℚ) * p7.resultant p6 =
      (-1 : ℚ) ^ (9 * 7) * (1 : ℚ) ^ 7 * p7.resultant p6 by norm_num]
  apply resultant_step (m := 9) (n := 7) (d := 6)
    (q := X ^ 2 + C 2 * X)
  · simp only [p9]
    compute_degree!
  · simp only [p7]
    compute_degree!
  · simp only [p6]
    compute_degree!
  · norm_num
  · simp only [p7]
    monicity!
  · norm_num
  · have hq : (X ^ 2 + C 2 * X : ℚ[X]).natDegree = 2 := by
      compute_degree!
    omega
  · simp [p9, p7, p6]
    ring_nf
    norm_num
    simp only [C_eq_smul_one]
    simp only [smul_mul_assoc]
    simp only [one_mul]
    module

private lemma res7_6 :
    p7.resultant p6 = (-1 : ℚ) ^ 6 * p6.resultant p2 := by
  rw [show (-1 : ℚ) ^ 6 * p6.resultant p2 =
      (-1 : ℚ) ^ (7 * 6) * (-1 : ℚ) ^ 6 * p6.resultant p2 by norm_num]
  apply resultant_step (m := 7) (n := 6) (d := 2)
    (q := X + C (-1))
  · simp only [p7]
    compute_degree!
  · simp only [p6]
    compute_degree!
  · simp only [p2]
    compute_degree!
  · norm_num
  · simp only [p6]
    monicity!
  · norm_num
  · have hq : (X + C (-1) : ℚ[X]).natDegree = 1 := by
      compute_degree!
    omega
  · simp [p7, p6, p2]
    ring_nf

private lemma res6_2 :
    p6.resultant p2 = (-2 : ℚ) ^ 2 * p2.resultant p1 := by
  rw [show (-2 : ℚ) ^ 2 * p2.resultant p1 =
      (-1 : ℚ) ^ (6 * 2) * (-2 : ℚ) ^ 2 * p2.resultant p1 by norm_num]
  apply resultant_step (m := 6) (n := 2) (d := 1)
    (q := X ^ 4 - X ^ 3 + C 2 * X ^ 2 - C 2 * X + C 2)
  · simp only [p6]
    compute_degree!
  · simp only [p2]
    compute_degree!
  · simp only [p1]
    compute_degree!
  · norm_num
  · simp only [p2]
    monicity!
  · norm_num
  · have hq :
        (X ^ 4 - X ^ 3 + C 2 * X ^ 2 - C 2 * X + C 2 :
          ℚ[X]).natDegree = 4 := by
      compute_degree!
    omega
  · simp [p6, p2, p1]
    ring_nf
    simp only [← Polynomial.C_mul]
    norm_num
    simp only [C_eq_smul_one]
    simp only [smul_mul_assoc]
    simp only [one_mul]
    module

private lemma res2_1 :
    p2.resultant p1 = (3 / 4 : ℚ) * p1.resultant p0 := by
  rw [show (3 / 4 : ℚ) * p1.resultant p0 =
      (-1 : ℚ) ^ (2 * 1) * (3 / 4 : ℚ) ^ 1 * p1.resultant p0 by norm_num]
  apply resultant_step (m := 2) (n := 1) (d := 0)
    (q := X + C (3 / 2))
  · simp only [p2]
    compute_degree!
  · simp only [p1]
    compute_degree!
  · simp only [p0]
    compute_degree!
  · norm_num
  · simp only [p1]
    monicity!
  · norm_num
  · have hq : (X + C (3 / 2) : ℚ[X]).natDegree = 1 := by
      compute_degree!
    omega
  · simp [p2, p1, p0]
    ring_nf
    simp only [← Polynomial.C_mul]
    norm_num
    simp only [C_eq_smul_one]
    simp only [smul_mul_assoc]
    simp only [one_mul]
    module

private lemma resultant_oddCharacterRootPolynomial_p10 :
    oddCharacterRootPolynomial.resultant p10 =
      3 * 46 ^ 10 / (5 : ℚ) ^ 11 := by
  rw [res11_10, res10_9, res9_7, res7_6, res6_2, res2_1]
  simp [p1, p0]
  norm_num

/-- The residue-weighted polynomial
`sum_(k=0)^21 (5^k mod 23) X^k` used for odd-character sums. -/
def characterSumPolynomial : ℚ[X] :=
  C 1 + C 5 * X + C 2 * X ^ 2 + C 10 * X ^ 3 + C 4 * X ^ 4 +
    C 20 * X ^ 5 + C 8 * X ^ 6 + C 17 * X ^ 7 + C 16 * X ^ 8 +
      C 11 * X ^ 9 + C 9 * X ^ 10 + C 22 * X ^ 11 + C 18 * X ^ 12 +
        C 21 * X ^ 13 + C 13 * X ^ 14 + C 19 * X ^ 15 + C 3 * X ^ 16 +
          C 15 * X ^ 17 + C 6 * X ^ 18 + C 7 * X ^ 19 + C 12 * X ^ 20 +
            C 14 * X ^ 21

private def initialQuotient : ℚ[X] :=
  C 22 + C 18 * X + C 21 * X ^ 2 + C 13 * X ^ 3 + C 19 * X ^ 4 +
    C 3 * X ^ 5 + C 15 * X ^ 6 + C 6 * X ^ 7 + C 7 * X ^ 8 +
      C 12 * X ^ 9 + C 14 * X ^ 10

/-- The exact odd-character resultant at `23`. -/
theorem characterSumPolynomial_resultant :
    oddCharacterRootPolynomial.resultant characterSumPolynomial =
      -3 * 46 ^ 10 := by
  have hdeq :
      characterSumPolynomial =
        C (-5) * p10 + oddCharacterRootPolynomial * initialQuotient := by
    simp [characterSumPolynomial, initialQuotient,
      oddCharacterRootPolynomial, p10]
    ring_nf
    simp only [← Polynomial.C_mul]
    norm_num
    simp only [C_eq_smul_one]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [one_mul, mul_one]
    module
  have h11 : oddCharacterRootPolynomial.natDegree = 11 := by
    simp only [oddCharacterRootPolynomial]
    compute_degree!
  have h21 : characterSumPolynomial.natDegree = 21 := by
    simp only [characterSumPolynomial]
    compute_degree!
  have h10 : (C (-5) * p10).natDegree = 10 := by
    rw [natDegree_C_mul (by norm_num)]
    simp only [p10]
    compute_degree!
  rw [show oddCharacterRootPolynomial.resultant characterSumPolynomial =
      oddCharacterRootPolynomial.resultant characterSumPolynomial 11 21 by
        simp [h11, h21]]
  rw [hdeq]
  rw [resultant_add_mul_right _ _ _ _ _ (by
    have hq : initialQuotient.natDegree = 10 := by
      simp only [initialQuotient]
      compute_degree!
    omega) (by simp [h11])]
  rw [show 21 = 10 + 11 by omega]
  rw [resultant_add_right_deg _ _ _ _ 11 h10.le]
  have hcoeff : oddCharacterRootPolynomial.coeff 11 = 1 := by
    simp [oddCharacterRootPolynomial, Polynomial.coeff_X_pow,
      Polynomial.coeff_one]
  rw [hcoeff, one_pow, one_mul]
  rw [resultant_C_mul_right]
  rw [show oddCharacterRootPolynomial.resultant p10 11 10 =
      oddCharacterRootPolynomial.resultant p10 by
    simp only [h11]
    have hp10 : p10.natDegree = 10 := by
      simp only [p10]
      compute_degree!
    simp [hp10]]
  rw [resultant_oddCharacterRootPolynomial_p10]
  norm_num

/-- The normalized finite product encoded by the odd-character resultant is
exactly `3`. -/
theorem normalizedCharacterSumProduct :
    -(oddCharacterRootPolynomial.resultant characterSumPolynomial) /
        (46 : ℚ) ^ 10 = 3 := by
  rw [characterSumPolynomial_resultant]
  norm_num

end

end BealRegular.TwentyThreeRelativeClassNumberResultant
