import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Eisenstein certificates for the exceptional seven-adic models

This module proves irreducibility of the septic and radical polynomials that
occur in the seven-adic classification for signature `(3,5,7)`.  The direct
`Q_7` endpoints cover `X^7 + 7cX + 7` for every seven-adically integral
`c` (that is, `‖c‖ ≤ 1`), and
`X^n - 7b` for every seven-adic unit `b` and positive `n`.

These results certify that the explicit model quotients are fields of their
advertised degrees once a local fiber has been identified with those models.
They do not prove that identification, the finite case classification, or the
exceptional local discriminant exponents.
-/

namespace BealRegular.Signature357SevenAdicEisenstein

open Polynomial
open scoped Ring

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

noncomputable section

/-- The maximal ideal of the seven-adic integers. -/
def sevenAdicMaximalIdeal : Ideal ℤ_[7] :=
  IsLocalRing.maximalIdeal ℤ_[7]

private theorem sevenAdicMaximalIdeal_isPrime :
    sevenAdicMaximalIdeal.IsPrime :=
  (IsLocalRing.maximalIdeal.isMaximal ℤ_[7]).isPrime

/-- Seven belongs to the maximal ideal of `Z_7`, but not to its square. -/
theorem seven_not_mem_maximalIdeal_sq :
    (7 : ℤ_[7]) ∉ sevenAdicMaximalIdeal ^ 2 := by
  rw [sevenAdicMaximalIdeal, PadicInt.maximalIdeal_eq_span_p,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have h7ne : (7 : ℤ_[7]) ≠ 0 := by norm_num
  have hone : (1 : ℤ_[7]) = 7 * c := by
    apply mul_left_cancel₀ h7ne
    calc
      (7 : ℤ_[7]) * 1 = 7 := by rw [mul_one]
      _ = 7 ^ 2 * c := hc
      _ = 7 * (7 * c) := by ring
  have hmem : (1 : ℤ_[7]) ∈ sevenAdicMaximalIdeal := by
    rw [hone]
    simpa [mul_comm] using
      sevenAdicMaximalIdeal.mul_mem_left c (by
        rw [sevenAdicMaximalIdeal, PadicInt.maximalIdeal_eq_span_p,
          Ideal.mem_span_singleton]
        exact (dvd_rfl : (7 : ℤ_[7]) ∣ 7))
  exact sevenAdicMaximalIdeal_isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr hmem)

/-- The integral septic model `X^7 + 7cX + 7`. -/
def septicIntegralPolynomial (c : ℤ_[7]) : ℤ_[7][X] :=
  X ^ 7 + (C (7 * c) * X + C 7)

private theorem septicIntegralPolynomial_monic (c : ℤ_[7]) :
    (septicIntegralPolynomial c).Monic := by
  rw [septicIntegralPolynomial]
  apply monic_X_pow_add
  exact degree_linear_le.trans_lt (by norm_num)

private theorem septicIntegralPolynomial_natDegree (c : ℤ_[7]) :
    (septicIntegralPolynomial c).natDegree = 7 := by
  rw [septicIntegralPolynomial]
  have hlt :
      (C (7 * c) * X + C 7 : ℤ_[7][X]).natDegree <
        ((X : ℤ_[7][X]) ^ 7).natDegree := by
    rw [natDegree_X_pow]
    exact natDegree_linear_le.trans_lt (by norm_num)
  rw [natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_X_pow]

/-- The integral septic model is Eisenstein at the maximal ideal of `Z_7`. -/
theorem septicIntegralPolynomial_isEisenstein (c : ℤ_[7]) :
    (septicIntegralPolynomial c).IsEisensteinAt sevenAdicMaximalIdeal := by
  apply (septicIntegralPolynomial_monic c).isEisensteinAt_of_mem_of_notMem
  · exact sevenAdicMaximalIdeal_isPrime.ne_top
  · intro n hn
    rw [septicIntegralPolynomial_natDegree] at hn
    interval_cases n <;>
      simp [septicIntegralPolynomial, sevenAdicMaximalIdeal,
        PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
  · simpa [septicIntegralPolynomial] using seven_not_mem_maximalIdeal_sq

private theorem septicIntegralPolynomial_map_irreducible (c : ℤ_[7]) :
    Irreducible
      ((septicIntegralPolynomial c).map (algebraMap ℤ_[7] ℚ_[7])) := by
  rw [← (septicIntegralPolynomial_monic c).irreducible_iff_irreducible_map_fraction_map]
  exact (septicIntegralPolynomial_isEisenstein c).irreducible
    sevenAdicMaximalIdeal_isPrime
    (septicIntegralPolynomial_monic c).isPrimitive
    (by rw [septicIntegralPolynomial_natDegree]; norm_num)

/-- The integral radical model `X^n - 7b`. -/
def radicalIntegralPolynomial (n : ℕ) (b : ℤ_[7]) : ℤ_[7][X] :=
  X ^ n - C (7 * b)

private theorem radicalIntegralPolynomial_monic {n : ℕ} (b : ℤ_[7])
    (hn : 0 < n) :
    (radicalIntegralPolynomial n b).Monic := by
  rw [radicalIntegralPolynomial]
  exact monic_X_pow_sub_C _ hn.ne'

private theorem radicalIntegralPolynomial_natDegree (n : ℕ) (b : ℤ_[7]) :
    (radicalIntegralPolynomial n b).natDegree = n := by
  rw [radicalIntegralPolynomial, natDegree_X_pow_sub_C]

/-- If `b` is a seven-adic unit and `n` is positive, the integral radical
model is Eisenstein at the maximal ideal of `Z_7`. -/
theorem radicalIntegralPolynomial_isEisenstein {n : ℕ} (b : ℤ_[7])
    (hn : 0 < n) (hb : IsUnit b) :
    (radicalIntegralPolynomial n b).IsEisensteinAt sevenAdicMaximalIdeal := by
  apply (radicalIntegralPolynomial_monic b hn).isEisensteinAt_of_mem_of_notMem
  · exact sevenAdicMaximalIdeal_isPrime.ne_top
  · intro i hi
    rw [radicalIntegralPolynomial_natDegree] at hi
    cases i with
    | zero =>
        have hn0 : (0 : ℕ) ≠ n := Nat.ne_of_lt hn
        simp [radicalIntegralPolynomial, hn0, sevenAdicMaximalIdeal,
          PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    | succ i =>
        have hne : i + 1 ≠ n := Nat.ne_of_lt hi
        simp [radicalIntegralPolynomial, hne]
  · intro hconst
    have hn0 : (0 : ℕ) ≠ n := Nat.ne_of_lt hn
    have hneg : -(7 * b) ∈ sevenAdicMaximalIdeal ^ 2 := by
      simpa [radicalIntegralPolynomial, hn0] using hconst
    have hpos : (7 : ℤ_[7]) * b ∈ sevenAdicMaximalIdeal ^ 2 := by
      have h := (sevenAdicMaximalIdeal ^ 2).neg_mem hneg
      simpa using h
    exact seven_not_mem_maximalIdeal_sq
      ((sevenAdicMaximalIdeal ^ 2).mul_unit_mem_iff_mem hb |>.mp hpos)

private theorem radicalIntegralPolynomial_map_irreducible {n : ℕ}
    (b : ℤ_[7]) (hn : 0 < n) (hb : IsUnit b) :
    Irreducible
      ((radicalIntegralPolynomial n b).map (algebraMap ℤ_[7] ℚ_[7])) := by
  rw [← (radicalIntegralPolynomial_monic b hn).irreducible_iff_irreducible_map_fraction_map]
  exact (radicalIntegralPolynomial_isEisenstein b hn hb).irreducible
    sevenAdicMaximalIdeal_isPrime
    (radicalIntegralPolynomial_monic b hn).isPrimitive
    (by rw [radicalIntegralPolynomial_natDegree]; exact hn)

/-- Direct septic Eisenstein endpoint over the seven-adic field. -/
theorem septicSevenAdic_irreducible (c : ℚ_[7]) (hc : ‖c‖ ≤ 1) :
    Irreducible (X ^ 7 + C (7 * c) * X + C 7 : ℚ_[7][X]) := by
  let ci : ℤ_[7] := ⟨c, hc⟩
  have h := septicIntegralPolynomial_map_irreducible ci
  have h7 : algebraMap ℤ_[7] ℚ_[7] (7 : ℤ_[7]) = (7 : ℚ_[7]) := rfl
  rw [septicIntegralPolynomial, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_C, map_mul, h7,
    PadicInt.algebraMap_apply] at h
  simpa [ci, add_assoc] using h

/-- Direct radical Eisenstein endpoint over the seven-adic field. -/
theorem radicalSevenAdic_irreducible {n : ℕ} (b : ℚ_[7])
    (hn : 0 < n) (hb : ‖b‖ = 1) :
    Irreducible (X ^ n - C (7 * b) : ℚ_[7][X]) := by
  let bi : ℤ_[7] := ⟨b, hb.le⟩
  have hbi : IsUnit bi := by
    rw [PadicInt.isUnit_iff]
    exact hb
  have h := radicalIntegralPolynomial_map_irreducible bi hn hbi
  have h7 : algebraMap ℤ_[7] ℚ_[7] (7 : ℤ_[7]) = (7 : ℚ_[7]) := rfl
  rw [radicalIntegralPolynomial, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, map_mul, h7,
    PadicInt.algebraMap_apply] at h
  simpa [bi] using h

end

end BealRegular.Signature357SevenAdicEisenstein
