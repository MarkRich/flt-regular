import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Tactic

/-!
# Gaussian-cube parametrization for the signature `(4, 4, 3)`

For coprime natural numbers `x` and `y` with `x ^ 4 + y ^ 4` odd, a solution
of

`x ^ 4 + y ^ 4 = z ^ 3`

makes the Gaussian integer `x ^ 2 + y ^ 2 * I` a cube.  Comparing real and
imaginary coordinates gives the classical two-parameter identities recorded
by `primitive_sum_square_cube_parametrization`.

This module supplies only that Gaussian factorization and parametrization
layer.  It does not prove the subsequent descent or rule out solutions of the
signature `(4, 4, 3)`.
-/

@[expose] public section

namespace BealRegular.GaussianCubeParametrization

local notation "ℤ[i]" => GaussianInt

noncomputable local instance : GCDMonoid ℤ[i] :=
  EuclideanDomain.gcdMonoid ℤ[i]

/-- A Gaussian integer of norm one has fourth power one. -/
lemma gaussian_pow_four_of_norm_eq_one (w : ℤ[i]) (hw : w.norm = 1) :
    w ^ 4 = 1 := by
  rcases w with ⟨a, b⟩
  simp [Zsqrtd.norm] at hw
  have ha_lower : -1 ≤ a := by nlinarith [sq_nonneg a]
  have ha_upper : a ≤ 1 := by nlinarith [sq_nonneg a]
  have hb_lower : -1 ≤ b := by nlinarith [sq_nonneg b]
  have hb_upper : b ≤ 1 := by nlinarith [sq_nonneg b]
  interval_cases a <;> interval_cases b <;> norm_num at hw
  all_goals norm_num [Zsqrtd.ext_iff, pow_succ]

/-- Every Gaussian unit is a cube: on the cyclic group of four units, cubing
is an automorphism. -/
lemma gaussian_unit_is_cube (u : ℤ[i]ˣ) :
    ∃ v : ℤ[i], (u : ℤ[i]) = v ^ 3 := by
  have hu4 : (u : ℤ[i]) ^ 4 = 1 :=
    gaussian_pow_four_of_norm_eq_one _
      ((Zsqrtd.norm_eq_one_iff' (by norm_num) (u : ℤ[i])).2 u.isUnit)
  refine ⟨(u : ℤ[i]) ^ 3, ?_⟩
  calc
    (u : ℤ[i]) = (u : ℤ[i]) ^ 9 := by
      nth_rewrite 1 [← pow_one (u : ℤ[i])]
      rw [show (9 : ℕ) = 1 + 4 * 2 by omega, pow_add, pow_mul, hu4, one_pow,
        mul_one]
    _ = ((u : ℤ[i]) ^ 3) ^ 3 := by ring

/-- The Gaussian integer `x ^ 2 + y ^ 2 * I`. -/
def squareGaussian (x y : ℕ) : ℤ[i] :=
  ⟨(x ^ 2 : ℕ), (y ^ 2 : ℕ)⟩

@[simp] lemma squareGaussian_re (x y : ℕ) :
    (squareGaussian x y).re = x ^ 2 := rfl

@[simp] lemma squareGaussian_im (x y : ℕ) :
    (squareGaussian x y).im = y ^ 2 := rfl

/-- The norm of `squareGaussian x y` is `x ^ 4 + y ^ 4`. -/
lemma natAbs_norm_squareGaussian (x y : ℕ) :
    (squareGaussian x y).norm.natAbs = x ^ 4 + y ^ 4 := by
  apply Nat.cast_injective (R := ℤ)
  rw [Int.natAbs_of_nonneg (GaussianInt.norm_nonneg _)]
  simp [squareGaussian, Zsqrtd.norm]
  ring

/-- The norm of the sum with the conjugate is `4 * x ^ 4`. -/
lemma natAbs_norm_squareGaussian_add_star (x y : ℕ) :
    (squareGaussian x y + star (squareGaussian x y)).norm.natAbs =
      4 * x ^ 4 := by
  apply Nat.cast_injective (R := ℤ)
  rw [Int.natAbs_of_nonneg (GaussianInt.norm_nonneg _)]
  simp [squareGaussian, Zsqrtd.norm]
  ring

/-- The norm of the difference with the conjugate is `4 * y ^ 4`. -/
lemma natAbs_norm_squareGaussian_sub_star (x y : ℕ) :
    (squareGaussian x y - star (squareGaussian x y)).norm.natAbs =
      4 * y ^ 4 := by
  apply Nat.cast_injective (R := ℤ)
  rw [Int.natAbs_of_nonneg (GaussianInt.norm_nonneg _)]
  simp [squareGaussian, Zsqrtd.norm]
  ring

/-- Divisibility in the Gaussian integers descends to divisibility of the
absolute values of norms. -/
lemma natAbs_norm_dvd_natAbs_norm_of_dvd {a b : ℤ[i]} (h : a ∣ b) :
    a.norm.natAbs ∣ b.norm.natAbs := by
  obtain ⟨c, rfl⟩ := h
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  exact dvd_mul_right _ _

/-- Under the primitive and odd-norm hypotheses, `x ^ 2 + y ^ 2 * I` is
coprime to its Gaussian conjugate. -/
lemma squareGaussian_isCoprime_star {x y : ℕ}
    (hxy : x.Coprime y) (hnormOdd : Odd (x ^ 4 + y ^ 4)) :
    IsCoprime (squareGaussian x y) (star (squareGaussian x y)) := by
  apply isCoprime_of_dvd (squareGaussian x y) (star (squareGaussian x y))
  · intro hzero
    have hnormZero : x ^ 4 + y ^ 4 = 0 := by
      rw [← natAbs_norm_squareGaussian]
      simp [hzero.1]
    exact (hnormOdd.pos.ne' hnormZero)
  · intro d hdNonunit hd0 hdLeft hdRight
    apply hdNonunit
    have hdAdd : d ∣ squareGaussian x y + star (squareGaussian x y) :=
      dvd_add hdLeft hdRight
    have hdSub : d ∣ squareGaussian x y - star (squareGaussian x y) :=
      dvd_sub hdLeft hdRight
    have hdx : d.norm.natAbs ∣ 4 * x ^ 4 := by
      simpa [natAbs_norm_squareGaussian_add_star] using
        natAbs_norm_dvd_natAbs_norm_of_dvd hdAdd
    have hdy : d.norm.natAbs ∣ 4 * y ^ 4 := by
      simpa [natAbs_norm_squareGaussian_sub_star] using
        natAbs_norm_dvd_natAbs_norm_of_dvd hdSub
    have hxyPow : (x ^ 4).Coprime (y ^ 4) := hxy.pow 4 4
    have hfour : d.norm.natAbs ∣ 4 := by
      have hgcd : Nat.gcd (4 * x ^ 4) (4 * y ^ 4) = 4 := by
        rw [Nat.gcd_mul_left, hxyPow.gcd_eq_one, mul_one]
      exact hgcd ▸ Nat.dvd_gcd hdx hdy
    have hdnorm : d.norm.natAbs ∣ x ^ 4 + y ^ 4 := by
      simpa [natAbs_norm_squareGaussian] using
        natAbs_norm_dvd_natAbs_norm_of_dvd hdLeft
    have hcop : Nat.Coprime 4 (x ^ 4 + y ^ 4) := by
      simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using
        hnormOdd.coprime_two_left.pow_left 2
    exact Zsqrtd.norm_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop hfour hdnorm)

/-- A `(4, 4, 3)` equation becomes a product of conjugate Gaussian integers
equal to a cube. -/
lemma squareGaussian_mul_star_eq_cube {x y z : ℕ}
    (h : x ^ 4 + y ^ 4 = z ^ 3) :
    squareGaussian x y * star (squareGaussian x y) = (z : ℤ[i]) ^ 3 := by
  rw [Zsqrtd.mul_star]
  apply Zsqrtd.ext
  · simp only [Zsqrtd.re_sub, Zsqrtd.re_mul, Zsqrtd.re_intCast,
      Zsqrtd.im_intCast, mul_zero]
    simp [squareGaussian, pow_succ]
    norm_cast
    ring_nf at h ⊢
    exact h
  · simp [squareGaussian, pow_succ]

/-- In the Gaussian integers, coprime conjugate factors whose product is a
cube force the first factor itself to be a cube. -/
lemma exists_gaussian_cube_eq_of_coprime_mul_star_eq_cube
    {a c : ℤ[i]} (hcop : IsCoprime a (star a)) (h : a * star a = c ^ 3) :
    ∃ w : ℤ[i], a = w ^ 3 := by
  have hgcd : IsUnit (gcd a (star a)) := (gcd_isUnit_iff _ _).2 hcop
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow hgcd h
  obtain ⟨u, hu⟩ := hd
  obtain ⟨v, hv⟩ := gaussian_unit_is_cube u
  refine ⟨d * v, ?_⟩
  calc
    a = d ^ 3 * (u : ℤ[i]) := hu.symm
    _ = d ^ 3 * v ^ 3 := by rw [hv]
    _ = (d * v) ^ 3 := by rw [mul_pow]

/-- A primitive odd-norm solution of `x ^ 4 + y ^ 4 = z ^ 3` admits the
classical Gaussian-cube coordinate parametrization.  This theorem does not
perform the later descent needed to rule out such solutions. -/
theorem primitive_sum_square_cube_parametrization {x y z : ℕ}
    (hxy : x.Coprime y) (hnormOdd : Odd (x ^ 4 + y ^ 4))
    (h : x ^ 4 + y ^ 4 = z ^ 3) :
    ∃ a b : ℤ,
      IsCoprime a b ∧
      (x : ℤ) ^ 2 = a * (a ^ 2 - 3 * b ^ 2) ∧
      (y : ℤ) ^ 2 = b * (3 * a ^ 2 - b ^ 2) := by
  obtain ⟨w, hw⟩ := exists_gaussian_cube_eq_of_coprime_mul_star_eq_cube
    (squareGaussian_isCoprime_star hxy hnormOdd)
    (squareGaussian_mul_star_eq_cube h)
  refine ⟨w.re, w.im, ?_, ?_, ?_⟩
  · have hcoords : IsCoprime (squareGaussian x y).re
        (squareGaussian x y).im := by
      simpa using Nat.isCoprime_iff_coprime.mpr (hxy.pow 2 2)
    apply Zsqrtd.isCoprime_of_dvd_isCoprime hcoords
    refine ⟨w ^ 2, ?_⟩
    calc
      squareGaussian x y = w ^ 3 := hw
      _ = w ^ 2 * w := by
        simpa only [Nat.reduceAdd] using (pow_succ w 2)
      _ = w * w ^ 2 := mul_comm _ _
  · have hre := congrArg Zsqrtd.re hw
    simp only [squareGaussian_re] at hre
    simp [pow_succ] at hre
    ring_nf at hre ⊢
    exact hre
  · have him := congrArg Zsqrtd.im hw
    simp only [squareGaussian_im] at him
    simp [pow_succ] at him
    ring_nf at him ⊢
    exact him

end BealRegular.GaussianCubeParametrization
