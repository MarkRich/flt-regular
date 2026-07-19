import BealRegular.Signature357GenericLocalPolynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Polynomial.Basic

/-!
# The real fiber of the signature `(3,5,7)` polynomial

For the degree-seven polynomial `phi`, the derivative is
`105 * x^4 * (x - 1)^2`.  It is nonnegative everywhere and positive away
from the two isolated critical points `0` and `1`.  By proving strict
monotonicity on the three intervals cut out by those points and joining the
pieces using global monotonicity, this module proves that `phi` is strictly
increasing on the real line.

The positive leading coefficient and odd degree then give surjectivity.
Consequently every real fiber `phi(X) - u` has exactly one real root.  This is
the substantive real-root input to Lemma 4.1(i) of the signature `(3,5,7)`
argument.

The result does not yet identify the full real algebra with
`ℝ × ℂ × ℂ × ℂ`; that requires factorization, complex-field classification,
and CRT bookkeeping.  It also does not constrain the degrees of global
number-field factors, classify discriminants, exclude signature `(3,5,7)`,
or prove Beal's conjecture.
-/

namespace BealRegular.Signature357RealFiber

open Filter Polynomial Set Topology
open Signature357GenericLocalPolynomial

noncomputable section

/-- The real specialization of the signature `(3,5,7)` polynomial `phi`. -/
abbrev phiReal : ℝ[X] := phiK (K := ℝ)

/-- The exact real derivative formula for the signature `(3,5,7)`
polynomial. -/
theorem phiReal_deriv (x : ℝ) :
    deriv (fun y : ℝ ↦ phiReal.eval y) x =
      105 * (x ^ 4 * (x - 1) ^ 2) := by
  rw [Polynomial.deriv]
  have h := fiberK_derivative (K := ℝ) (0 : ℝ)
  have h' : phiReal.derivative =
      105 * (X ^ 4 * (X - C 1) ^ 2) := by
    simpa only [fiberK, C_0, sub_zero] using h
  rw [h']
  simp

private theorem phiReal_deriv_nonneg (x : ℝ) :
    0 ≤ deriv (fun y : ℝ ↦ phiReal.eval y) x := by
  rw [phiReal_deriv]
  positivity

private theorem phiReal_deriv_pos {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    0 < deriv (fun y : ℝ ↦ phiReal.eval y) x := by
  rw [phiReal_deriv]
  positivity

private theorem phiReal_monotone :
    Monotone (fun x : ℝ ↦ phiReal.eval x) :=
  monotone_of_deriv_nonneg phiReal.differentiable phiReal_deriv_nonneg

private theorem phiReal_strictMonoOn_left :
    StrictMonoOn (fun x : ℝ ↦ phiReal.eval x) (Iic 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic 0) phiReal.continuous.continuousOn
  intro x hx
  rw [interior_Iic] at hx
  have hx' : x < 0 := by simpa only [mem_Iio] using hx
  exact phiReal_deriv_pos hx'.ne (ne_of_lt (hx'.trans (by norm_num)))

private theorem phiReal_strictMonoOn_middle :
    StrictMonoOn (fun x : ℝ ↦ phiReal.eval x) (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) phiReal.continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  exact phiReal_deriv_pos hx.1.ne' hx.2.ne

private theorem phiReal_strictMonoOn_right :
    StrictMonoOn (fun x : ℝ ↦ phiReal.eval x) (Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) phiReal.continuous.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  have hx' : 1 < x := by simpa only [mem_Ioi] using hx
  exact phiReal_deriv_pos
    (ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans hx')) hx'.ne'

/-- The signature `(3,5,7)` polynomial is strictly increasing over the
reals, despite its derivative vanishing at `0` and `1`. -/
theorem phiReal_strictMono :
    StrictMono (fun x : ℝ ↦ phiReal.eval x) := by
  intro x y hxy
  by_cases hy0 : y ≤ 0
  · exact phiReal_strictMonoOn_left (hxy.le.trans hy0) hy0 hxy
  by_cases hx0 : x < 0
  · exact (phiReal_strictMonoOn_left hx0.le (by simp) hx0).trans_le
      (phiReal_monotone (le_of_not_ge hy0))
  have hx0' : 0 ≤ x := le_of_not_gt hx0
  by_cases hy1 : y ≤ 1
  · exact phiReal_strictMonoOn_middle ⟨hx0', by linarith⟩
      ⟨by linarith, hy1⟩ hxy
  by_cases hx1 : x < 1
  · exact (phiReal_strictMonoOn_middle ⟨hx0', hx1.le⟩ (by simp) hx1).trans_le
      (phiReal_monotone (le_of_not_ge hy1))
  exact phiReal_strictMonoOn_right (le_of_not_gt hx1)
    ((le_of_not_gt hx1).trans hxy.le) hxy

/-- Evaluation of the signature `(3,5,7)` polynomial on the reals is
injective. -/
theorem phiReal_eval_injective :
    Function.Injective (fun x : ℝ ↦ phiReal.eval x) :=
  phiReal_strictMono.injective

private theorem phiReal_natDegree : phiReal.natDegree = 7 := by
  simpa [fiberK] using fiberK_natDegree (K := ℝ) (0 : ℝ)

private theorem phiReal_leadingCoeff : phiReal.leadingCoeff = 15 := by
  rw [leadingCoeff, phiReal_natDegree]
  norm_num [phiK]

private theorem phiReal_degree_pos : 0 < phiReal.degree := by
  rw [← natDegree_pos_iff_degree_pos, phiReal_natDegree]
  norm_num

private theorem phiReal_tendsto_atTop :
    Tendsto (fun x : ℝ ↦ phiReal.eval x) atTop atTop :=
  phiReal.tendsto_atTop_of_leadingCoeff_nonneg phiReal_degree_pos
    (phiReal_leadingCoeff.symm ▸ by norm_num)

private theorem pow_seven_tendsto_atBot :
    Tendsto (fun x : ℝ ↦ x ^ 7) atBot atBot := by
  have htop : Tendsto (fun x : ℝ ↦ (-x) ^ 7) atBot atTop :=
    (tendsto_pow_atTop (by norm_num)).comp tendsto_neg_atBot_atTop
  have hneg : Tendsto (fun x : ℝ ↦ -((-x) ^ 7)) atBot atBot :=
    tendsto_neg_atTop_atBot.comp htop
  simpa only [Odd.neg_pow (by decide : Odd 7), neg_neg] using hneg

private theorem phiReal_tendsto_atBot :
    Tendsto (fun x : ℝ ↦ phiReal.eval x) atBot atBot := by
  have hlead : Tendsto
      (fun x : ℝ ↦ phiReal.leadingCoeff * x ^ phiReal.natDegree)
      atBot atBot := by
    rw [phiReal_leadingCoeff, phiReal_natDegree]
    exact pow_seven_tendsto_atBot.const_mul_atBot (by norm_num)
  exact phiReal.isEquivalent_atBot_lead.symm.tendsto_atBot hlead

/-- Evaluation of the signature `(3,5,7)` polynomial on the reals is
surjective. -/
theorem phiReal_eval_surjective :
    Function.Surjective (fun x : ℝ ↦ phiReal.eval x) :=
  phiReal.continuous.surjective phiReal_tendsto_atTop phiReal_tendsto_atBot

/-- Every real fiber of the signature `(3,5,7)` polynomial has exactly one
real root. -/
theorem fiberReal_existsUniqueRoot (u : ℝ) :
    ∃! x : ℝ, (fiberK (K := ℝ) u).IsRoot x := by
  obtain ⟨x, hx⟩ := phiReal_eval_surjective u
  refine ⟨x, ?_, ?_⟩
  · simp [fiberK, hx]
  · intro y hy
    apply phiReal_eval_injective
    have hy' : phiReal.eval y = u := by
      have hy'' : phiReal.eval y - u = 0 := by
        simpa [fiberK] using hy
      linarith
    exact hy'.trans hx.symm

end


end BealRegular.Signature357RealFiber
