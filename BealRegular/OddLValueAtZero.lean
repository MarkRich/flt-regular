module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Odd Dirichlet `L`-values at zero

This file isolates the analytic continuation step that turns an odd periodic
function's value at zero into a finite weighted sum.  Mathlib already writes
that value as a finite sum of odd Hurwitz zeta functions.  Evaluating the
functional equation at zero reduces each Hurwitz term to `sinZeta a 1 / pi`.

The remaining pointwise identity is the conditionally convergent sawtooth
Fourier series at `s = 1`.  It is kept visible as the proposition
`ZMod.SinZetaOneSawtoothFormula`; this file neither assumes it globally nor
declares an axiom or instance for it.  Given a proof of that proposition, the
generic weighted-sum formula and its Dirichlet-character specialization follow.
-/

@[expose] public section

open Complex Filter Finset ZMod
open scoped Real

namespace HurwitzZeta

/-- At zero, the odd Hurwitz zeta function is the `s = 1` sine zeta value
divided by `pi`.  This is an unconditional specialization of Mathlib's
functional equation. -/
theorem hurwitzZetaOdd_apply_zero_eq_sinZeta_one_div_pi (a : UnitAddCircle) :
    hurwitzZetaOdd a 0 = sinZeta a 1 / (Real.pi : ℂ) := by
  have h := hurwitzZetaOdd_one_sub a (s := (1 : ℂ)) (by
    intro n hn
    have hn' := congrArg Complex.re hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    norm_num at hn'
    linarith)
  simp only [sub_self, cpow_neg_one, Gamma_one, mul_one] at h
  rw [Complex.sin_pi_div_two] at h
  rw [h]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

end HurwitzZeta

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- The missing `s = 1` endpoint of the sawtooth Fourier expansion, stated
pointwise on the nonzero residues modulo `N`.

This is a proposition, not an axiom or typeclass.  The zero residue is omitted:
oddness makes its contribution to the `L`-value vanish separately. -/
def SinZetaOneSawtoothFormula (N : ℕ) [NeZero N] : Prop :=
  ∀ j : ZMod N, j ≠ 0 →
    HurwitzZeta.sinZeta (toAddCircle j) 1 =
      (Real.pi : ℂ) * (1 / 2 - (j.val : ℂ) / N)

/-- An odd periodic function satisfying the pointwise sawtooth endpoint has
the standard finite weighted-sum formula for its analytically continued
`L`-value at zero. -/
theorem LFunction_apply_zero_of_odd_of_sinZeta_one
    (Φ : ZMod N → ℂ) (hΦ : Function.Odd Φ)
    (hsaw : SinZetaOneSawtoothFormula N) :
    LFunction Φ 0 = -(∑ j : ZMod N, Φ j * (j.val : ℂ)) / N := by
  rw [LFunction_def_odd hΦ, neg_zero, cpow_zero, one_mul]
  have hterm (j : ZMod N) :
      Φ j * HurwitzZeta.hurwitzZetaOdd (toAddCircle j) 0 =
        Φ j * (1 / 2 - (j.val : ℂ) / N) := by
    rcases eq_or_ne j 0 with rfl | hj
    · rw [hΦ.map_zero]
      simp
    · rw [HurwitzZeta.hurwitzZetaOdd_apply_zero_eq_sinZeta_one_div_pi,
        hsaw j hj]
      field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  simp_rw [hterm]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hΦ.sum_eq_zero, zero_mul, zero_sub]
  simp_rw [div_eq_mul_inv, ← mul_assoc]
  rw [← Finset.sum_mul]
  ring

end ZMod

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- The weighted-sum formula for an odd complex Dirichlet character, with the
sole Fourier endpoint retained as an ordinary theorem parameter. -/
theorem Odd.LFunction_apply_zero_of_sinZeta_one
    {χ : DirichletCharacter ℂ N} (hχ : χ.Odd)
    (hsaw : ZMod.SinZetaOneSawtoothFormula N) :
    LFunction χ 0 = -(∑ j : ZMod N, χ j * (j.val : ℂ)) / N := by
  exact ZMod.LFunction_apply_zero_of_odd_of_sinZeta_one χ hχ.to_fun hsaw

end DirichletCharacter
