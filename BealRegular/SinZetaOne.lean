module

public import BealRegular.OddLValueAtZero
public import BealRegular.SawtoothFourier
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# The sine-zeta boundary value at one

This file identifies Mathlib's analytically continued sine zeta function at
`s = 1` with the natural-order sawtooth Fourier series.  The main analytic
input is an Abelian boundary theorem for `LSeries`: bounded coefficient partial
sums and convergence of the naturally ordered series at `s = 1` determine the
limit from the half-plane `re s > 1`.  Continuity of `HurwitzZeta.sinZeta` then
identifies its analytically continued value.

For nonzero residues modulo `N`, the representative `j.val / N` lies strictly
between zero and one.  The boundary theorem therefore proves
`ZMod.SinZetaOneSawtoothFormula N` without hypotheses and removes the final
parameter from the odd `L(0)` weighted-sum formula.

This closes the sine-zeta endpoint only.  It does not construct the missing
factorization of the cyclotomic Dedekind zeta function into Dirichlet
`L`-functions, nor does it evaluate the finite product over all odd characters.
-/

@[expose] public section

open Complex Filter Finset MeasureTheory Asymptotics
open scoped Topology Real

namespace Complex

/-- Dominated convergence for the partial-sum integral in the Abelian
boundary argument, as a real exponent approaches `1` from the right. -/
theorem tendsto_integral_partial_cpow_nhdsWithin_one
    {c : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, c k‖ ≤ C) :
    Tendsto
      (fun s : ℝ ↦ ∫ (t : ℝ) in Set.Ioi 1,
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (t : ℂ) ^ (-(s : ℂ) - 1))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds (∫ (t : ℝ) in Set.Ioi 1,
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (t : ℂ) ^ (-2 : ℂ))) := by
  let S : ℝ → ℂ := fun t ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k
  let F : ℝ → ℝ → ℂ := fun s t ↦ S t * (t : ℂ) ^ (-(s : ℂ) - 1)
  let g : ℝ → ℝ := fun t ↦ C * t ^ (-2 : ℝ)
  have hg : Integrable g (volume.restrict (Set.Ioi (1 : ℝ))) := by
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul C
  have hmeas : Filter.Eventually
      (fun s : ℝ ↦ AEStronglyMeasurable (F s) (volume.restrict (Set.Ioi (1 : ℝ))))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) := by
    filter_upwards with s
    have hpow : LocallyIntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-(s : ℂ) - 1))
        (Set.Ici 1) := by
      refine ContinuousOn.locallyIntegrableOn (fun t ht ↦ ?_) measurableSet_Ici
      exact (continuousAt_ofReal_cpow_const t (-(s : ℂ) - 1)
        (Or.inr (zero_lt_one.trans_le ht).ne')).continuousWithinAt
    simpa only [F, S, mul_comm] using
      ((locallyIntegrableOn_mul_sum_Icc (m := 1) c zero_le_one hpow).mono_set
        Set.Ioi_subset_Ici_self).aestronglyMeasurable
  have hdom : Filter.Eventually
      (fun s : ℝ ↦ ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : ℝ))), ‖F s t‖ ≤ g t)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) := by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have ht1 : 1 ≤ t := ht.le
    have hs1 : 1 < s := hs
    have hSt : ‖S t‖ ≤ C := by simpa only [S] using hbound ⌊t⌋₊
    change ‖S t * (t : ℂ) ^ (-(s : ℂ) - 1)‖ ≤ C * t ^ (-2 : ℝ)
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [neg_re, sub_re, ofReal_re, one_re]
    calc
      ‖S t‖ * t ^ (-s - 1) ≤ C * t ^ (-s - 1) :=
        mul_le_mul_of_nonneg_right hSt (Real.rpow_nonneg ht0.le _)
      _ ≤ C * t ^ (-2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) hC
  have hlim : ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      Tendsto (fun s : ℝ ↦ F s t) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
        (nhds (S t * (t : ℂ) ^ (-2 : ℂ))) := by
    filter_upwards with t
    apply tendsto_nhdsWithin_of_tendsto_nhds
    change Tendsto (fun s : ℝ ↦ S t * (t : ℂ) ^ (-(s : ℂ) - 1))
      (nhds 1) (nhds (S t * (t : ℂ) ^ (-2 : ℂ)))
    have he : Tendsto (fun s : ℝ ↦ (-(s : ℂ) - 1)) (nhds 1) (nhds (-2 : ℂ)) := by
      convert ContinuousAt.tendsto (by fun_prop : ContinuousAt
        (fun s : ℝ ↦ (-(s : ℂ) - 1)) 1) using 1
      all_goals norm_num
    exact tendsto_const_nhds.mul
      (he.const_cpow (Or.inr (by norm_num : (-2 : ℂ) ≠ 0)))
  simpa only [S, F] using
    tendsto_integral_filter_of_dominated_convergence g hmeas hdom hg hlim

/-- The integral formula for an `LSeries` transfers a boundary value of its
partial-sum integral to the `LSeries` itself. -/
theorem tendsto_LSeries_real_nhdsWithin_one_of_boundary_integral
    {c : ℕ → ℂ} {C : ℝ} {l : ℂ} (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, c k‖ ≤ C)
    (hS : ∀ s : ℝ, 1 < s → LSeriesSummable c s)
    (hboundary : (∫ (t : ℝ) in Set.Ioi 1,
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (t : ℂ) ^ (-2 : ℂ)) = l) :
    Tendsto (fun s : ℝ ↦ LSeries c s)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds l) := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, c k) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ)) := by
    refine isBigO_iff.mpr ⟨C, Eventually.of_forall (fun n ↦ ?_)⟩
    simpa using hbound n
  have hint := tendsto_integral_partial_cpow_nhdsWithin_one hC hbound
  rw [hboundary] at hint
  have hs_cast : Tendsto (fun s : ℝ ↦ (s : ℂ))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (1 : ℂ)) := by
    exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  have hprod := hs_cast.mul hint
  have heq : Filter.EventuallyEq (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (fun s : ℝ ↦ LSeries c s)
      (fun s : ℝ ↦ (s : ℂ) * ∫ (t : ℝ) in Set.Ioi 1,
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (t : ℂ) ^ (-(s : ℂ) - 1)) := by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    simpa only [neg_add_rev, add_comm, sub_eq_add_neg] using
      (LSeries_eq_mul_integral c (r := 0) (by norm_num)
        (by simpa using (zero_lt_one.trans hs)) (hS s hs) hO)
  simpa using hprod.congr' heq.symm

/-- Abel summation identifies the boundary integral with the natural-order
sum of `c k / k`. -/
theorem boundary_integral_eq_of_tendsto_sum_div
    {c : ℕ → ℂ} {C : ℝ} {l : ℂ} (hc : c 0 = 0)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, c k‖ ≤ C)
    (hsum : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, c k / (k : ℂ))
      atTop (nhds l)) :
    (∫ (t : ℝ) in Set.Ioi 1,
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (t : ℂ) ^ (-2 : ℂ)) = l := by
  let f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-1 : ℂ)
  have hsum_eq (n : ℕ) :
      ∑ k ∈ Finset.Icc 0 n, c k = ∑ k ∈ Finset.Icc 1 n, c k := by
    rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by aesop), hc,
      zero_add, zero_add]
  have hf_diff : ∀ t ∈ Set.Ici (1 : ℝ), DifferentiableAt ℝ f t := by
    intro t ht
    exact differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne'
      (by norm_num)
  have hf_int : LocallyIntegrableOn (deriv f) (Set.Ici (1 : ℝ)) volume := by
    refine (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi ?_).locallyIntegrableOn
    exact integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one (by norm_num)
  have hlim : Tendsto
      (fun n : ℕ ↦ f n * ∑ k ∈ Finset.Icc 0 n, c k) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hp : Tendsto (fun n : ℕ ↦ C * (n : ℝ) ^ (-1 : ℝ)) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul
        ((tendsto_rpow_neg_atTop zero_lt_one).comp tendsto_natCast_atTop_atTop))
    refine squeeze_zero' (Eventually.of_forall (fun n ↦ norm_nonneg _)) ?_ hp
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    change ‖(n : ℂ) ^ (-1 : ℂ) * ∑ k ∈ Finset.Icc 0 n, c k‖ ≤
      C * (n : ℝ) ^ (-1 : ℝ)
    rw [norm_mul, norm_natCast_cpow_of_re_ne_zero n (by norm_num), hsum_eq]
    simp only [neg_re, one_re]
    calc
      (n : ℝ) ^ (-1 : ℝ) * ‖∑ k ∈ Icc 1 n, c k‖ ≤
          (n : ℝ) ^ (-1 : ℝ) * C :=
        mul_le_mul_of_nonneg_left (hbound n) (Real.rpow_nonneg hn0.le _)
      _ = C * (n : ℝ) ^ (-1 : ℝ) := mul_comm _ _
  have hg_dom :
      (fun t : ℝ ↦ deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop]
        (fun t : ℝ ↦ t ^ (-2 : ℝ)) := by
    refine isBigO_iff.mpr ⟨C, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hSt : ‖∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ C := by
      rw [hsum_eq]
      exact hbound ⌊t⌋₊
    change ‖deriv (fun u : ℝ ↦ (u : ℂ) ^ (-1 : ℂ)) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k‖ ≤ C * ‖t ^ (-2 : ℝ)‖
    rw [deriv_ofReal_cpow_const ht0.ne' (by norm_num), norm_mul, norm_mul,
      norm_neg, norm_one, one_mul, norm_cpow_eq_rpow_re_of_pos ht0,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    rw [show ((-1 : ℂ) - 1).re = (-2 : ℝ) by norm_num]
    calc
      t ^ (-2 : ℝ) * ‖∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤ t ^ (-2 : ℝ) * C :=
        mul_le_mul_of_nonneg_left hSt (Real.rpow_nonneg ht0.le _)
      _ = C * t ^ (-2 : ℝ) := mul_comm _ _
  have hg_int : IntegrableAtFilter (fun t : ℝ ↦ t ^ (-2 : ℝ)) atTop volume :=
    integrableAtFilter_rpow_atTop_iff.mpr (by norm_num)
  have hab := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c hc hf_diff hf_int hlim
    hg_dom hg_int
  have hright :
      (0 - ∫ (t : ℝ) in Set.Ioi 1,
        deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      ∫ (t : ℝ) in Set.Ioi 1,
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (t : ℂ) ^ (-2 : ℂ) := by
    rw [zero_sub, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    change -(deriv (fun u : ℝ ↦ (u : ℂ) ^ (-1 : ℂ)) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (t : ℂ) ^ (-2 : ℂ)
    rw [deriv_ofReal_cpow_const ht0.ne' (by norm_num), hsum_eq]
    norm_num
    ring
  rw [hright] at hab
  have hab' : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, c k / (k : ℂ))
      atTop (nhds (∫ (t : ℝ) in Set.Ioi 1,
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) * (t : ℂ) ^ (-2 : ℂ))) := by
    convert hab using 1
    funext n
    rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by aesop), hc,
      mul_zero, zero_add]
    apply sum_congr rfl
    intro k hk
    simp only [f, cpow_neg_one, div_eq_mul_inv, mul_comm, ofReal_natCast]
  exact tendsto_nhds_unique hab' hsum

/-- A generic Abelian boundary theorem for complex `LSeries` at `s = 1`.
Bounded coefficient partial sums and convergence of the natural-order boundary
series imply convergence of the absolutely convergent values from the right. -/
theorem tendsto_LSeries_real_nhdsWithin_one
    {c : ℕ → ℂ} {C : ℝ} {l : ℂ} (hc : c 0 = 0) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, c k‖ ≤ C)
    (hsum : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, c k / (k : ℂ))
      atTop (nhds l))
    (hS : ∀ s : ℝ, 1 < s → LSeriesSummable c s) :
    Tendsto (fun s : ℝ ↦ LSeries c s)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds l) := by
  apply tendsto_LSeries_real_nhdsWithin_one_of_boundary_integral hC hbound hS
  exact boundary_integral_eq_of_tendsto_sum_div hc hbound hsum

/-- Uniform boundedness of sine-coefficient partial sums in the `Icc` indexing
used by the `LSeries` integral formula. -/
theorem norm_sum_sin_Icc_le {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, (Real.sin (2 * Real.pi * x * k) : ℂ)‖ ≤
      2 / ‖exp ((2 * Real.pi * x) * I) - 1‖ := by
  have h := norm_sum_sin_two_pi_mul_le_two_div_norm_exp_sub_one hx0 hx1 n
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) by ext k; simp,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right, Nat.add_comm, Nat.cast_add, Nat.cast_one]
  rw [← ofReal_sum, norm_real]
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The sawtooth Fourier limit from `SawtoothFourier.lean`, converted to the
complex coefficients and `Icc` indexing needed by the Abelian theorem. -/
theorem tendsto_sum_sin_Icc_div {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto
      (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
        (Real.sin (2 * Real.pi * x * k) : ℂ) / (k : ℂ))
      atTop (nhds ((Real.pi * (1 / 2 - x) : ℝ) : ℂ)) := by
  have hr := tendsto_sum_sin_two_pi_mul_div hx0 hx1
  have hc := (Complex.continuous_ofReal.tendsto (Real.pi * (1 / 2 - x))).comp hr
  convert hc using 1
  funext n
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) by ext k; simp,
    Finset.sum_Ico_eq_sum_range]
  simp only [Function.comp_apply]
  rw [ofReal_sum]
  simp only [Nat.add_sub_cancel_right]
  apply sum_congr rfl
  intro i hi
  simp only [Nat.add_comm]
  push_cast
  simp

/-- The sine `LSeries` tends to its sawtooth boundary value as a real exponent
approaches `1` from the absolutely convergent half-plane. -/
theorem tendsto_LSeries_sin_real_nhdsWithin_one {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto
      (fun s : ℝ ↦ LSeries (fun n : ℕ ↦
        (Real.sin (2 * Real.pi * x * n) : ℂ)) s)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds ((Real.pi * (1 / 2 - x) : ℝ) : ℂ)) := by
  let C : ℝ := 2 / ‖exp ((2 * Real.pi * x) * I) - 1‖
  apply tendsto_LSeries_real_nhdsWithin_one
      (C := C) (l := ((Real.pi * (1 / 2 - x) : ℝ) : ℂ))
  · simp
  · exact div_nonneg (by norm_num) (norm_nonneg _)
  · intro n
    exact norm_sum_sin_Icc_le hx0 hx1 n
  · exact tendsto_sum_sin_Icc_div hx0 hx1
  · intro s hs
    exact (HurwitzZeta.LSeriesHasSum_sin x (by simpa using hs)).LSeriesSummable

/-- Mathlib's analytic sine zeta function at `s = 1` equals the natural-order
sawtooth Fourier value for `0 < x < 1`. -/
theorem _root_.HurwitzZeta.sinZeta_one_eq_sawtooth
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HurwitzZeta.sinZeta (x : UnitAddCircle) 1 =
      ((Real.pi * (1 / 2 - x) : ℝ) : ℂ) := by
  let c : ℕ → ℂ := fun n ↦ (Real.sin (2 * Real.pi * x * n) : ℂ)
  have hL : Tendsto (fun s : ℝ ↦ LSeries c s)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds ((Real.pi * (1 / 2 - x) : ℝ) : ℂ)) := by
    exact tendsto_LSeries_sin_real_nhdsWithin_one hx0 hx1
  have heq : Filter.EventuallyEq (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (fun s : ℝ ↦ LSeries c s)
      (fun s : ℝ ↦ HurwitzZeta.sinZeta (x : UnitAddCircle) s) := by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    exact (HurwitzZeta.LSeriesHasSum_sin x (by simpa using hs)).LSeries_eq
  have hseries : Tendsto (fun s : ℝ ↦ HurwitzZeta.sinZeta (x : UnitAddCircle) s)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds ((Real.pi * (1 / 2 - x) : ℝ) : ℂ)) := hL.congr' heq
  have hcontℂ : Tendsto (HurwitzZeta.sinZeta (x : UnitAddCircle)) (nhds (1 : ℂ))
      (nhds (HurwitzZeta.sinZeta (x : UnitAddCircle) 1)) :=
    (HurwitzZeta.differentiableAt_sinZeta (x : UnitAddCircle) 1).continuousAt.tendsto
  have hcont : Tendsto (fun s : ℝ ↦ HurwitzZeta.sinZeta (x : UnitAddCircle) s)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds (HurwitzZeta.sinZeta (x : UnitAddCircle) 1)) := by
    exact (hcontℂ.comp (Complex.continuous_ofReal.tendsto 1)).mono_left
      nhdsWithin_le_nhds
  exact tendsto_nhds_unique hcont hseries

end Complex

namespace ZMod

variable (N : ℕ) [NeZero N]

/-- The sine-zeta sawtooth identity at a nonzero residue modulo `N`. -/
theorem sinZeta_one_eq_sawtooth (j : ZMod N) (hj : j ≠ 0) :
    HurwitzZeta.sinZeta (ZMod.toAddCircle j) 1 =
      (Real.pi : ℂ) * (1 / 2 - (j.val : ℂ) / N) := by
  have hN0 : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hj0 : 0 < (j.val : ℝ) := Nat.cast_pos.mpr (ZMod.val_pos.mpr hj)
  have hx0 : 0 < (j.val : ℝ) / N := div_pos hj0 hN0
  have hx1 : (j.val : ℝ) / N < 1 := by
    rw [div_lt_one hN0]
    exact_mod_cast ZMod.val_lt j
  have h := HurwitzZeta.sinZeta_one_eq_sawtooth hx0 hx1
  rw [← ZMod.toAddCircle_apply j] at h
  convert h using 1
  all_goals
    push_cast
    ring

/-- The pointwise sine-zeta proposition required by `OddLValueAtZero.lean`,
now proved for every nontrivial modulus. -/
theorem sinZetaOneSawtoothFormula : SinZetaOneSawtoothFormula N := by
  intro j hj
  exact sinZeta_one_eq_sawtooth N j hj

/-- The unconditional weighted-sum formula at zero for any odd function on
`ZMod N`. -/
theorem LFunction_apply_zero_of_odd (Phi : ZMod N → ℂ) (hPhi : Phi.Odd) :
    LFunction Phi 0 = -(∑ j : ZMod N, Phi j * (j.val : ℂ)) / N := by
  exact ZMod.LFunction_apply_zero_of_odd_of_sinZeta_one Phi hPhi
    (sinZetaOneSawtoothFormula N)

end ZMod

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- The unconditional weighted-sum formula at zero for an odd complex
Dirichlet character. -/
theorem Odd.LFunction_apply_zero_weighted_sum
    {chi : DirichletCharacter ℂ N} (hchi : chi.Odd) :
    LFunction chi 0 = -(∑ j : ZMod N, chi j * (j.val : ℂ)) / N := by
  exact Odd.LFunction_apply_zero_of_sinZeta_one hchi
    (ZMod.sinZetaOneSawtoothFormula N)

end DirichletCharacter
