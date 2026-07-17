module

public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The sawtooth Fourier series

This file proves the classical, conditionally convergent sawtooth Fourier
series in its natural order.  For `0 < x < 1`, the partial sums

`sum (i < n), sin (2 * pi * x * (i + 1)) / (i + 1)`

converge to `pi * (1 / 2 - x)`.  The proof first obtains convergence on the
unit circle by Dirichlet's test, identifies the Abel limit with the principal
complex logarithm, and then computes its imaginary part.

This theorem does not identify Mathlib's analytically continued
`HurwitzZeta.sinZeta x 1` with the natural-order series.  That boundary-value
identification remains a separate step before this result can discharge
`ZMod.SinZetaOneSawtoothFormula` from `OddLValueAtZero.lean`.
-/

@[expose] public section

open Complex Filter Finset
open scoped Topology

namespace Complex

/-- Geometric partial sums on the unit circle away from `1` are uniformly
bounded.  This is also a reusable bound for the sine-series coefficients after
taking imaginary parts. -/
theorem norm_sum_pow_succ_le_two_div_norm_sub_one
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, z ^ (i + 1)‖ ≤ 2 / ‖z - 1‖ := by
  rw [show (∑ i ∈ Finset.range n, z ^ (i + 1)) =
      z * (∑ i ∈ Finset.range n, z ^ i) by
    rw [Finset.mul_sum]
    congr 1 with i
    rw [pow_succ', mul_comm]]
  rw [geom_sum_eq hz1]
  rw [norm_mul, norm_div, hz, one_mul]
  exact div_le_div_of_nonneg_right (by
    calc
      ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num)
    (norm_nonneg _)

/-- The naturally ordered logarithmic power series converges at every point
of the unit circle except `1`.  This is the Dirichlet-test input to the Abel
limit argument below. -/
theorem exists_tendsto_sum_pow_succ_div_succ_of_norm_eq_one_ne_one
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ l : ℂ, Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, z ^ (i + 1) / (i + 1 : ℕ))
      atTop (nhds l) := by
  have hanti : Antitone (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) := by
    exact antitone_nat_of_succ_le fun n ↦ by
      rw [div_le_div_iff_of_pos_left zero_lt_one (by positivity) (by positivity)]
      norm_num
  have hzero : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (nhds 0) := by
    simp only [one_div]
    apply Tendsto.inv_tendsto_atTop
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  apply cauchySeq_tendsto_of_complete
  convert hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hzero
    (norm_sum_pow_succ_le_two_div_norm_sub_one hz hz1) using 1
  ext n
  congr 1 with i
  simp [div_eq_mul_inv, mul_comm]

/-- Inside the open unit disk, the shifted logarithmic power series sums to
the expected radial expression. -/
theorem tsum_pow_succ_div_succ_mul_pow_eq_neg_log_div
    {z : ℂ} (hz : ‖z‖ = 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∑' n : ℕ, z ^ (n + 1) / (n + 1 : ℕ) * (r : ℂ) ^ n) =
      -log (1 - z * r) / r := by
  have hnorm : ‖z * (r : ℂ)‖ < 1 := by
    rw [norm_mul, hz, one_mul, norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have ht := hasSum_taylorSeries_neg_log hnorm
  have hshift : HasSum
      (fun n : ℕ ↦ (z * (r : ℂ)) ^ (n + 1) / (n + 1 : ℕ))
      (-log (1 - z * r)) := by
    simpa [Nat.cast_add, Nat.cast_one] using (hasSum_nat_add_iff' 1).mpr ht
  refine ((hshift.div_const (r : ℂ)).congr_fun fun n ↦ ?_).tsum_eq
  rw [mul_pow, pow_succ', mul_div_assoc]
  field_simp [Complex.ofReal_ne_zero.mpr hr0.ne']
  ring

/-- Abel's theorem identifies the natural-order limit of the logarithmic
power series with the principal logarithm, provided the endpoint lies in its
slit plane. -/
theorem tendsto_sum_pow_succ_div_succ_eq_neg_log
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (hslit : 1 - z ∈ slitPlane) :
    Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, z ^ (i + 1) / (i + 1 : ℕ))
      atTop (nhds (-log (1 - z))) := by
  obtain ⟨l, hl⟩ :=
    exists_tendsto_sum_pow_succ_div_succ_of_norm_eq_one_ne_one hz hz1
  have hab := tendsto_tsum_powerSeries_nhdsWithin_lt hl
  rw [tendsto_map'_iff] at hab
  have heq :
      (fun r : ℝ ↦ ∑' n : ℕ,
        z ^ (n + 1) / (n + 1 : ℕ) * (r : ℂ) ^ n) =ᶠ[nhdsWithin (1 : ℝ) (Set.Iio 1)]
      (fun r : ℝ ↦ -log (1 - z * r) / r) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    exact tsum_pow_succ_div_succ_mul_pow_eq_neg_log_div hz hr.1 hr.2
  have hab' : Tendsto (fun r : ℝ ↦ -log (1 - z * r) / r)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds l) := hab.congr' heq
  have hc : ContinuousAt (fun r : ℝ ↦ -log (1 - z * r) / r) 1 := by
    have hinner : ContinuousAt (fun r : ℝ ↦ (1 : ℂ) - z * r) 1 := by fun_prop
    exact (hinner.clog (by simpa using hslit)).neg.div (by fun_prop) (by norm_num)
  have hcont : Tendsto (fun r : ℝ ↦ -log (1 - z * r) / r)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (-log (1 - z))) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have : l = -log (1 - z) := tendsto_nhds_unique hab' hcont
  simpa only [this] using hl

/-- The principal argument of `1 - exp (2 * pi * x * I)` for `0 < x < 1`.
This fixes the branch of the complex logarithm used by the Fourier proof. -/
theorem arg_one_sub_exp_two_pi_mul_I {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    arg (1 - exp ((2 * Real.pi * x) * I)) = Real.pi * x - Real.pi / 2 := by
  have hpx0 : 0 < Real.pi * x := mul_pos Real.pi_pos hx0
  have hpx1 : Real.pi * x < Real.pi := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hx1 Real.pi_pos
  have hsin : 0 < Real.sin (Real.pi * x) := Real.sin_pos_of_pos_of_lt_pi hpx0 hpx1
  have hang : Real.pi * x - Real.pi / 2 ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  rw [show 1 - exp ((2 * Real.pi * x) * I) =
      (2 * Real.sin (Real.pi * x) : ℝ) *
        (Complex.cos (Real.pi * x - Real.pi / 2 : ℝ) +
          Complex.sin (Real.pi * x - Real.pi / 2 : ℝ) * I) by
    rw [show (2 : ℂ) * Real.pi * x = ((2 * Real.pi * x : ℝ) : ℂ) by norm_num,
      exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos, ← ofReal_sin]
    apply Complex.ext
    · simp only [sub_re, one_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, sub_zero, zero_mul, add_zero]
      rw [Real.cos_sub_pi_div_two]
      have harg : 2 * Real.pi * x = 2 * (Real.pi * x) := by ring
      rw [harg, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
    · simp only [sub_im, one_im, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, mul_one, zero_add]
      rw [Real.sin_sub_pi_div_two]
      have harg : 2 * Real.pi * x = 2 * (Real.pi * x) := by ring
      rw [harg, Real.sin_two_mul]
      ring]
  exact arg_mul_cos_add_sin_mul_I (mul_pos two_pos hsin) hang

/-- For `0 < x < 1`, the corresponding point on the unit circle is not `1`.
This packages the endpoint check used by both the convergence and boundedness
theorems. -/
theorem exp_two_pi_mul_I_ne_one_of_pos_of_lt_one
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    exp ((2 * Real.pi * x) * I) ≠ 1 := by
  have hpx0 : 0 < Real.pi * x := mul_pos Real.pi_pos hx0
  have hpx1 : Real.pi * x < Real.pi := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hx1 Real.pi_pos
  have hsin : 0 < Real.sin (Real.pi * x) := Real.sin_pos_of_pos_of_lt_pi hpx0 hpx1
  intro h
  have hzero : ‖exp ((2 * Real.pi * x) * I) - 1‖ = 0 := by
    rw [h, sub_self, norm_zero]
  have hzero' : ‖exp (I * (2 * Real.pi * x : ℝ)) - 1‖ = 0 := by
    simpa [mul_comm] using hzero
  have hnorm := norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * x)
  rw [hzero'] at hnorm
  have hpos : 0 < ‖2 * Real.sin ((2 * Real.pi * x) / 2)‖ := by
    rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
    exact norm_pos_iff.mpr (mul_ne_zero two_ne_zero hsin.ne')
  linarith

/-- The imaginary part of a power of the unit-circle exponential is the
corresponding sine coefficient. -/
theorem im_exp_two_pi_mul_I_pow (x : ℝ) (n : ℕ) :
    ((exp ((2 * Real.pi * x) * I)) ^ (n + 1)).im =
      Real.sin (2 * Real.pi * x * (n + 1)) := by
  rw [← exp_nat_mul]
  rw [show ((n + 1 : ℕ) : ℂ) * ((2 : ℂ) * Real.pi * x * I) =
      ((2 * Real.pi * x * (n + 1) : ℝ) : ℂ) * I by
    push_cast
    ring]
  rw [exp_ofReal_mul_I_im]

/-- The imaginary part of a term of the complex logarithmic power series is
the corresponding term of the sine series. -/
theorem im_exp_two_pi_mul_I_pow_div (x : ℝ) (n : ℕ) :
    ((exp ((2 * Real.pi * x) * I)) ^ (n + 1) / (n + 1 : ℕ)).im =
      Real.sin (2 * Real.pi * x * (n + 1)) / (n + 1 : ℝ) := by
  rw [← exp_nat_mul]
  rw [show ((n + 1 : ℕ) : ℂ) * ((2 : ℂ) * Real.pi * x * I) =
      ((2 * Real.pi * x * (n + 1) : ℝ) : ℂ) * I by
    push_cast
    ring]
  rw [div_natCast_im, exp_ofReal_mul_I_im]
  norm_num

/-- Sine partial sums are uniformly bounded for `0 < x < 1`.  This is the
real-coefficient form of `norm_sum_pow_succ_le_two_div_norm_sub_one` and can be
used directly in boundary-limit arguments for the sine zeta function. -/
theorem norm_sum_sin_two_pi_mul_le_two_div_norm_exp_sub_one
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * x * (i + 1))‖ ≤
      2 / ‖exp ((2 * Real.pi * x) * I) - 1‖ := by
  let z : ℂ := exp ((2 * Real.pi * x) * I)
  have hz : ‖z‖ = 1 := by
    simpa [z] using norm_exp_ofReal_mul_I (2 * Real.pi * x)
  have hz1 : z ≠ 1 := by
    simpa [z] using exp_two_pi_mul_I_ne_one_of_pos_of_lt_one hx0 hx1
  have hbound := norm_sum_pow_succ_le_two_div_norm_sub_one hz hz1 n
  calc
    ‖∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * x * (i + 1))‖ =
        ‖(∑ i ∈ Finset.range n, z ^ (i + 1)).im‖ := by
      congr 1
      rw [Complex.im_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simpa [z] using (im_exp_two_pi_mul_I_pow x i).symm
    _ ≤ ‖∑ i ∈ Finset.range n, z ^ (i + 1)‖ := by
      simpa only [Real.norm_eq_abs] using
        abs_im_le_norm (∑ i ∈ Finset.range n, z ^ (i + 1))
    _ ≤ 2 / ‖exp ((2 * Real.pi * x) * I) - 1‖ := by
      simpa [z] using hbound

/-- The classical sawtooth Fourier series in natural order: for `0 < x < 1`,
the `n`th partial sum of `sin (2 * pi * k * x) / k` tends to
`pi * (1 / 2 - x)`. -/
theorem tendsto_sum_sin_two_pi_mul_div {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n,
        Real.sin (2 * Real.pi * x * (i + 1)) / (i + 1 : ℝ))
      atTop (nhds (Real.pi * (1 / 2 - x))) := by
  let z : ℂ := exp ((2 * Real.pi * x) * I)
  have hpx0 : 0 < Real.pi * x := mul_pos Real.pi_pos hx0
  have hpx1 : Real.pi * x < Real.pi := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hx1 Real.pi_pos
  have hz : ‖z‖ = 1 := by
    simpa [z] using norm_exp_ofReal_mul_I (2 * Real.pi * x)
  have hz1 : z ≠ 1 := by
    simpa [z] using exp_two_pi_mul_I_ne_one_of_pos_of_lt_one hx0 hx1
  have harg : arg (1 - z) = Real.pi * x - Real.pi / 2 := by
    exact arg_one_sub_exp_two_pi_mul_I hx0 hx1
  have hslit : 1 - z ∈ slitPlane := by
    rw [mem_slitPlane_iff_arg, harg]
    exact ⟨by linarith [Real.pi_pos], sub_ne_zero.mpr hz1.symm⟩
  have hc := tendsto_sum_pow_succ_div_succ_eq_neg_log hz hz1 hslit
  have him := (continuous_im.tendsto (-log (1 - z))).comp hc
  have hleft (n : ℕ) :
      (∑ i ∈ Finset.range n, z ^ (i + 1) / (i + 1 : ℕ)).im =
        ∑ i ∈ Finset.range n,
          Real.sin (2 * Real.pi * x * (i + 1)) / (i + 1 : ℝ) := by
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact im_exp_two_pi_mul_I_pow_div x i
  have hright : (-log (1 - z)).im = Real.pi * (1 / 2 - x) := by
    rw [neg_im, log_im, harg]
    ring
  convert him using 1
  · funext n
    exact (hleft n).symm
  · exact congrArg nhds hright.symm

end Complex
