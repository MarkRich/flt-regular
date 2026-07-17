import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

/-!
# Infinite descent for the quartic-three-square auxiliary equation

This module proves that no nonzero coprime natural numbers `u` and `v` can
satisfy `u ^ 4 = 3 * v ^ 4 + w ^ 2`.  The theorem is an unconditional
auxiliary result for the reduced Beal signature `(4, 4, 3)`.  Connecting the
Gaussian-cube parametrization to these exact natural-number hypotheses is a
separate bridge.
-/

namespace BealRegular.QuarticThreeDescent

/-- Two coprime natural numbers cannot both be even. -/
theorem not_both_even_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    ¬(Even m ∧ Even n) := by
  rintro ⟨hm, hn⟩
  have htwo : 2 = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (even_iff_two_dvd.mp hm) (even_iff_two_dvd.mp hn)
  omega

/-- For nonzero exponents, parity of a power equation reduces to parity of bases. -/
theorem even_C_iff_even_A_iff_even_B {A B C x y z : ℕ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hEq : A ^ x + B ^ y = C ^ z) :
    Even C ↔ (Even A ↔ Even B) := by
  rw [← Nat.even_pow' hz, ← hEq, Nat.even_add,
    Nat.even_pow' hx, Nat.even_pow' hy]

/-- Data for a primitive solution of the auxiliary quartic-three equation. -/
structure PrimitiveQuarticThreeData where
  x : ℕ
  y : ℕ
  q : ℕ
  x_ne_zero : x ≠ 0
  y_ne_zero : y ≠ 0
  coprime_xy : Nat.Coprime x y
  equation : x ^ 4 = 3 * y ^ 4 + q ^ 2


/-! ## The modulo-sixteen entry to the descent -/

private theorem zmod16_no_quartic_three_square_with_odd_second :
    ∀ x y z : ZMod 16,
      IsUnit y → x ^ 4 ≠ 3 * y ^ 4 + z ^ 2 := by
  decide

private theorem isUnit_zmod16_of_not_even {n : ℕ} (hn : ¬Even n) :
    IsUnit (n : ZMod 16) := by
  rw [ZMod.isUnit_iff_coprime]
  have h2 : ¬2 ∣ n := by simpa only [even_iff_two_dvd] using hn
  simpa only [show 16 = 2 ^ 4 by norm_num] using
    Nat.prime_two.coprime_pow_of_not_dvd h2 (m := 4)

/-- In a primitive positive solution of `x^4 = 3*y^4 + z^2`, the second
quartic base is even. -/
theorem quarticThree_even_y {x y z : ℕ}
    (hEq : x ^ 4 = 3 * y ^ 4 + z ^ 2) : Even y := by
  by_contra hy
  have hEqZ : (x : ZMod 16) ^ 4 =
      3 * (y : ZMod 16) ^ 4 + (z : ZMod 16) ^ 2 := by
    simpa only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ZMod 16)) hEq
  exact zmod16_no_quartic_three_square_with_odd_second _ _ _
    (isUnit_zmod16_of_not_even hy) hEqZ

/-! ## Coprimality and order -/

/-- Coprimality of `x,y` propagates to `x,z` in the primitive quartic-three
equation.  The key observation is that `gcd(x,z)^2` divides `3`, since it is
coprime to `y^4`. -/
theorem quarticThree_coprime_x_z {x y z : ℕ}
    (hxy : Nat.Coprime x y)
    (hEq : x ^ 4 = 3 * y ^ 4 + z ^ 2) : Nat.Coprime x z := by
  let d := Nat.gcd x z
  have hdx : d ∣ x := Nat.gcd_dvd_left x z
  have hdz : d ∣ z := Nat.gcd_dvd_right x z
  have hd2x4 : d ^ 2 ∣ x ^ 4 := by
    obtain ⟨a, ha⟩ := hdx
    use d ^ 2 * a ^ 4
    rw [ha]
    ring
  have hd2z2 : d ^ 2 ∣ z ^ 2 := by
    obtain ⟨b, hb⟩ := hdz
    use b ^ 2
    rw [hb]
    ring
  have hz2le : z ^ 2 ≤ x ^ 4 := by omega
  have hdiff : x ^ 4 - z ^ 2 = 3 * y ^ 4 := by omega
  have hd2threeY : d ^ 2 ∣ 3 * y ^ 4 := by
    rw [← hdiff]
    exact Nat.dvd_sub hd2x4 hd2z2
  have hdy : Nat.Coprime d y :=
    Nat.Coprime.of_dvd_left hdx hxy
  have hd2y4 : Nat.Coprime (d ^ 2) (y ^ 4) := hdy.pow 2 4
  have hd2three : d ^ 2 ∣ 3 :=
    hd2y4.dvd_of_dvd_mul_right hd2threeY
  have hdne : d ≠ 0 := by
    intro hd
    simp only [hd, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_dvd_iff] at hd2three
    omega
  have hdle : d ^ 2 ≤ 3 := Nat.le_of_dvd (by norm_num) hd2three
  have hdOne : d = 1 := by
    have hdpos : 0 < d := Nat.pos_of_ne_zero hdne
    nlinarith
  exact Nat.coprime_iff_gcd_eq_one.mpr hdOne

/-- Positivity of `y` makes the square term strictly smaller than `x^4`, so
`z < x^2`. -/
theorem quarticThree_z_lt_x_sq {x y z : ℕ} (hy : y ≠ 0)
    (hEq : x ^ 4 = 3 * y ^ 4 + z ^ 2) : z < x ^ 2 := by
  have hy4pos : 0 < 3 * y ^ 4 := by positivity
  have hzpow : z ^ 2 < x ^ 4 := by omega
  have hzpow' : z ^ 2 < (x ^ 2) ^ 2 := by
    simpa only [show x ^ 4 = (x ^ 2) ^ 2 by ring] using hzpow
  exact (Nat.pow_lt_pow_iff_left (n := 2) (by norm_num)).mp hzpow'

/-! ## Exact factor gcd and coprime halves -/

/-- The product of the two natural difference-of-squares factors is exactly
`3*y^4`. -/
theorem quarticThree_factor_product {x y z : ℕ}
    (hEq : x ^ 4 = 3 * y ^ 4 + z ^ 2) :
    (x ^ 2 + z) * (x ^ 2 - z) = 3 * y ^ 4 := by
  have hdiff : x ^ 4 - z ^ 2 = 3 * y ^ 4 := by omega
  calc
    (x ^ 2 + z) * (x ^ 2 - z) = (x ^ 2) ^ 2 - z ^ 2 :=
      (Nat.sq_sub_sq (x ^ 2) z).symm
    _ = x ^ 4 - z ^ 2 := by ring_nf
    _ = 3 * y ^ 4 := hdiff

/-- In a primitive positive solution, the two factors
`x^2+z` and `x^2-z` have gcd exactly two. -/
theorem quarticThree_factor_gcd_eq_two {x y z : ℕ}
    (hy : y ≠ 0) (hxy : Nat.Coprime x y)
    (hEq : x ^ 4 = 3 * y ^ 4 + z ^ 2) :
    Nat.gcd (x ^ 2 + z) (x ^ 2 - z) = 2 := by
  have hyEven : Even y := quarticThree_even_y hEq
  have hxNotEven : ¬Even x := by
    intro hxEven
    exact not_both_even_of_coprime hxy ⟨hxEven, hyEven⟩
  have hxOdd : Odd x := Nat.not_even_iff_odd.mp hxNotEven
  have hparity : Even x ↔ (Even (3 * y ^ 4) ↔ Even z) := by
    have h := even_C_iff_even_A_iff_even_B
      (A := 3 * y ^ 4) (B := z) (C := x)
      (x := 1) (y := 2) (z := 4)
      (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [pow_one] using hEq.symm)
    simpa only [Nat.even_pow' (by norm_num : (4 : ℕ) ≠ 0),
      Nat.even_pow' (by norm_num : (2 : ℕ) ≠ 0)] using h
  have hThreeYEven : Even (3 * y ^ 4) := by
    exact (hyEven.pow_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)).mul_left 3
  have hzNotEven : ¬Even z := by
    intro hzEven
    have : Even x := hparity.mpr (iff_of_true hThreeYEven hzEven)
    exact hxNotEven this
  have hzOdd : Odd z := Nat.not_even_iff_odd.mp hzNotEven
  have hxz : Nat.Coprime x z := quarticThree_coprime_x_z hxy hEq
  have hx2z : Nat.Coprime (x ^ 2) z := hxz.pow_left 2
  have hAddZ : Nat.Coprime (x ^ 2 + z) z :=
    Nat.coprime_add_self_left.mpr hx2z
  let d := Nat.gcd (x ^ 2 + z) (x ^ 2 - z)
  have hdAdd : d ∣ x ^ 2 + z := Nat.gcd_dvd_left _ _
  have hdSub : d ∣ x ^ 2 - z := Nat.gcd_dvd_right _ _
  have hzle : z ≤ x ^ 2 := (quarticThree_z_lt_x_sq hy hEq).le
  have hTwoZ : (x ^ 2 + z) - (x ^ 2 - z) = 2 * z := by omega
  have hdTwoZ : d ∣ 2 * z := by
    simpa only [hTwoZ] using Nat.dvd_sub hdAdd hdSub
  have hdCopZ : Nat.Coprime d z :=
    Nat.Coprime.of_dvd_left hdAdd hAddZ
  have hdTwo : d ∣ 2 := hdCopZ.dvd_of_dvd_mul_right hdTwoZ
  have hAddEven : Even (x ^ 2 + z) := hxOdd.pow.add_odd hzOdd
  have hSubEven : Even (x ^ 2 - z) := hxOdd.pow.tsub_odd hzOdd
  have hTwoD : 2 ∣ d := Nat.dvd_gcd
    (even_iff_two_dvd.mp hAddEven) (even_iff_two_dvd.mp hSubEven)
  exact Nat.dvd_antisymm hdTwo hTwoD

/-- Removing the exact common factor two makes the two descent factors
coprime. -/
theorem quarticThree_halves_coprime {x y z : ℕ}
    (hy : y ≠ 0) (hxy : Nat.Coprime x y)
    (hEq : x ^ 4 = 3 * y ^ 4 + z ^ 2) :
    Nat.Coprime ((x ^ 2 + z) / 2) ((x ^ 2 - z) / 2) := by
  have hgcd := quarticThree_factor_gcd_eq_two hy hxy hEq
  have h := Nat.coprime_div_gcd_div_gcd
    (m := x ^ 2 + z) (n := x ^ 2 - z) (by simp [hgcd])
  simpa only [hgcd] using h

/-- Exact product identity for the two coprime halves.  This is the arithmetic
starting point for allocating the factors `3` and `2^2` and extracting fourth
powers in the classical infinite descent. -/
theorem quarticThree_halves_product {x y z : ℕ}
    (hEq : x ^ 4 = 3 * y ^ 4 + z ^ 2) :
    ((x ^ 2 + z) / 2) * ((x ^ 2 - z) / 2) =
      3 * (y ^ 2 / 2) ^ 2 := by
  have hyEven : Even y := quarticThree_even_y hEq
  have hxyParity : Even x ↔ Even z := by
    have h := even_C_iff_even_A_iff_even_B
      (A := 3 * y ^ 4) (B := z) (C := x)
      (x := 1) (y := 2) (z := 4)
      (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [pow_one] using hEq.symm)
    have hThreeYEven : Even (3 * y ^ 4) :=
      (hyEven.pow_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)).mul_left 3
    have h' : Even x ↔ (Even (3 * y ^ 4) ↔ Even z) := by
      simpa only [Nat.even_pow' (by norm_num : (4 : ℕ) ≠ 0),
        Nat.even_pow' (by norm_num : (2 : ℕ) ≠ 0)] using h
    constructor
    · intro hx
      exact (h'.mp hx).mp hThreeYEven
    · intro hz
      exact h'.mpr (iff_of_true hThreeYEven hz)
  have hAddEven : Even (x ^ 2 + z) := by
    rw [Nat.even_add, Nat.even_pow' (by norm_num : (2 : ℕ) ≠ 0)]
    exact hxyParity
  have hzle : z ≤ x ^ 2 := by
    have : z ^ 2 ≤ x ^ 4 := by omega
    have : z ^ 2 ≤ (x ^ 2) ^ 2 := by
      simpa only [show x ^ 4 = (x ^ 2) ^ 2 by ring] using this
    exact (Nat.pow_le_pow_iff_left (n := 2) (by norm_num)).mp this
  have hSubEven : Even (x ^ 2 - z) := by
    rw [Nat.even_sub hzle, Nat.even_pow' (by norm_num : (2 : ℕ) ≠ 0)]
    exact hxyParity
  have hAddSplit : 2 * ((x ^ 2 + z) / 2) = x ^ 2 + z :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp hAddEven)
  have hSubSplit : 2 * ((x ^ 2 - z) / 2) = x ^ 2 - z :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp hSubEven)
  have hRaw := quarticThree_factor_product hEq
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4)
  calc
    4 * (((x ^ 2 + z) / 2) * ((x ^ 2 - z) / 2)) =
        (2 * ((x ^ 2 + z) / 2)) * (2 * ((x ^ 2 - z) / 2)) := by ring
    _ = (x ^ 2 + z) * (x ^ 2 - z) := by rw [hAddSplit, hSubSplit]
    _ = 3 * y ^ 4 := hRaw
    _ = 4 * (3 * (y ^ 2 / 2) ^ 2) := by
      obtain ⟨k, rfl⟩ := hyEven
      have hk : (k + k) ^ 2 / 2 = 2 * k ^ 2 := by
        have hpow : (k + k) ^ 2 = 2 * (2 * k ^ 2) := by ring
        rw [hpow]
        omega
      rw [hk]
      ring


/-! ## A reusable prime-times-square split -/

/-- Coprime factors of a natural square are themselves squares.  The chosen
nonnegative square roots remain coprime and their product is the original
root. -/
theorem coprime_mul_eq_sq_split {u v w : ℕ}
    (huv : Nat.Coprime u v) (h : u * v = w ^ 2) :
    ∃ r s : ℕ, Nat.Coprime r s ∧
      u = r ^ 2 ∧ v = s ^ 2 ∧ w = r * s := by
  have hInt : (u : ℤ) * (v : ℤ) = (w : ℤ) ^ 2 := by
    exact_mod_cast h
  obtain ⟨r, hr⟩ := Int.sq_of_isCoprime huv.isCoprime hInt
  obtain ⟨s, hs⟩ := Int.sq_of_isCoprime
    (isCoprime_comm.mp huv.isCoprime) (by simpa only [mul_comm] using hInt)
  have hru : u = r.natAbs ^ 2 := by
    rcases hr with hr | hr
    · simpa only [← Int.natAbs_pow, Int.natAbs_natCast] using
        congrArg Int.natAbs hr
    · simpa only [Int.natAbs_neg, ← Int.natAbs_pow, Int.natAbs_natCast] using
        congrArg Int.natAbs hr
  have hsv : v = s.natAbs ^ 2 := by
    rcases hs with hs | hs
    · simpa only [← Int.natAbs_pow, Int.natAbs_natCast] using
        congrArg Int.natAbs hs
    · simpa only [Int.natAbs_neg, ← Int.natAbs_pow, Int.natAbs_natCast] using
        congrArg Int.natAbs hs
  have hrsCop : Nat.Coprime r.natAbs s.natAbs := by
    have hPow : Nat.Coprime (r.natAbs ^ 2) (s.natAbs ^ 2) := by
      simpa only [← hru, ← hsv] using huv
    rw [Nat.coprime_pow_left_iff (by norm_num : 0 < 2),
      Nat.coprime_pow_right_iff (by norm_num : 0 < 2)] at hPow
    exact hPow
  refine ⟨r.natAbs, s.natAbs, hrsCop, hru, hsv, ?_⟩
  apply Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)
  calc
    w ^ 2 = u * v := h.symm
    _ = r.natAbs ^ 2 * s.natAbs ^ 2 := by rw [hru, hsv]
    _ = (r.natAbs * s.natAbs) ^ 2 := by ring

/-- If two coprime natural numbers multiply to a prime times a square, then
the prime belongs to exactly one factor and the remaining parts are squares.
The square roots remain coprime and multiply exactly to the original square
root. -/
theorem coprime_mul_eq_prime_mul_sq_split {p u v w : ℕ}
    (hp : p.Prime) (huv : Nat.Coprime u v)
    (h : u * v = p * w ^ 2) :
    (∃ r s : ℕ, Nat.Coprime r s ∧
      u = p * r ^ 2 ∧ v = s ^ 2 ∧ w = r * s) ∨
    (∃ r s : ℕ, Nat.Coprime r s ∧
      u = r ^ 2 ∧ v = p * s ^ 2 ∧ w = r * s) := by
  have hpDvd : p ∣ u * v := by
    rw [h]
    exact dvd_mul_right p (w ^ 2)
  rcases hp.dvd_mul.mp hpDvd with hpu | hpv
  · obtain ⟨u', hu'⟩ := hpu
    have hu'v : Nat.Coprime u' v :=
      Nat.Coprime.of_dvd_left ⟨p, by simp [hu', Nat.mul_comm]⟩ huv
    have hSquare : u' * v = w ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      calc
        p * (u' * v) = (p * u') * v := by ring
        _ = u * v := by rw [hu']
        _ = p * w ^ 2 := h
    obtain ⟨r, s, hrsCop, hru, hsv, hrs⟩ :=
      coprime_mul_eq_sq_split hu'v hSquare
    left
    refine ⟨r, s, hrsCop, ?_, hsv, hrs⟩
    rw [hu', hru]
  · obtain ⟨v', hv'⟩ := hpv
    have huv' : Nat.Coprime u v' :=
      Nat.Coprime.of_dvd_right ⟨p, by simp [hv', Nat.mul_comm]⟩ huv
    have hSquare : u * v' = w ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      calc
        p * (u * v') = u * (p * v') := by ring
        _ = u * v := by rw [hv']
        _ = p * w ^ 2 := h
    obtain ⟨r, s, hrsCop, hru, hsv, hrs⟩ :=
      coprime_mul_eq_sq_split huv' hSquare
    right
    refine ⟨r, s, hrsCop, hru, ?_, hrs⟩
    rw [hv', hsv]

/-! ## Exact fourth-power allocations -/

/-- For an even natural number, the half of its square is twice the square
of its half. -/
theorem even_sq_div_two {y : ℕ} (hy : Even y) :
    y ^ 2 / 2 = 2 * (y / 2) ^ 2 := by
  obtain ⟨k, rfl⟩ := hy
  have hHalf : (k + k) / 2 = k := by omega
  have hpow : (k + k) ^ 2 = 2 * (2 * k ^ 2) := by ring
  rw [hHalf, hpow]
  omega

/-- The two descent halves add back to `x^2`. -/
theorem quarticThree_halves_sum {x y z : ℕ}
    (hy : y ≠ 0) (hxy : Nat.Coprime x y)
    (hEq : x ^ 4 = 3 * y ^ 4 + z ^ 2) :
    (x ^ 2 + z) / 2 + (x ^ 2 - z) / 2 = x ^ 2 := by
  have hgcd := quarticThree_factor_gcd_eq_two hy hxy hEq
  have hAddDvd : 2 ∣ x ^ 2 + z := by
    have := Nat.gcd_dvd_left (x ^ 2 + z) (x ^ 2 - z)
    simpa only [hgcd] using this
  have hSubDvd : 2 ∣ x ^ 2 - z := by
    have := Nat.gcd_dvd_right (x ^ 2 + z) (x ^ 2 - z)
    simpa only [hgcd] using this
  have hAdd : 2 * ((x ^ 2 + z) / 2) = x ^ 2 + z :=
    Nat.mul_div_cancel' hAddDvd
  have hSub : 2 * ((x ^ 2 - z) / 2) = x ^ 2 - z :=
    Nat.mul_div_cancel' hSubDvd
  have hzle : z ≤ x ^ 2 := (quarticThree_z_lt_x_sq hy hEq).le
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
  calc
    2 * ((x ^ 2 + z) / 2 + (x ^ 2 - z) / 2) =
        2 * ((x ^ 2 + z) / 2) + 2 * ((x ^ 2 - z) / 2) := by ring
    _ = (x ^ 2 + z) + (x ^ 2 - z) := by rw [hAdd, hSub]
    _ = 2 * x ^ 2 := by omega

/-- The raw four-way allocation obtained by splitting the coprime halves at
`3`, then splitting their coprime square roots at `2`.  Besides the two half
identities, this records the root product `y / 2 = a*b`, which is needed by
the next descent step. -/
theorem quarticThree_four_allocations {x y z : ℕ}
    (hy : y ≠ 0) (hxy : Nat.Coprime x y)
    (hEq : x ^ 4 = 3 * y ^ 4 + z ^ 2) :
    ∃ a b : ℕ, Nat.Coprime a b ∧ y / 2 = a * b ∧
      ((((x ^ 2 + z) / 2 = 12 * a ^ 4) ∧
          ((x ^ 2 - z) / 2 = b ^ 4)) ∨
       (((x ^ 2 + z) / 2 = 3 * a ^ 4) ∧
          ((x ^ 2 - z) / 2 = 4 * b ^ 4)) ∨
       (((x ^ 2 + z) / 2 = 4 * a ^ 4) ∧
          ((x ^ 2 - z) / 2 = 3 * b ^ 4)) ∨
       (((x ^ 2 + z) / 2 = a ^ 4) ∧
          ((x ^ 2 - z) / 2 = 12 * b ^ 4))) := by
  have hCop := quarticThree_halves_coprime hy hxy hEq
  have hProd := quarticThree_halves_product hEq
  rcases coprime_mul_eq_prime_mul_sq_split Nat.prime_three hCop hProd with
      ⟨r, s, hrsCop, hP, hQ, hRoot⟩ |
      ⟨r, s, hrsCop, hP, hQ, hRoot⟩
  · have hRootProd : r * s = 2 * (y / 2) ^ 2 := by
      rw [← hRoot, even_sq_div_two (quarticThree_even_y hEq)]
    rcases coprime_mul_eq_prime_mul_sq_split Nat.prime_two hrsCop hRootProd with
        ⟨a, b, hab, hra, hsb, ht⟩ | ⟨a, b, hab, hra, hsb, ht⟩
    · refine ⟨a, b, hab, ht, Or.inl ⟨?_, ?_⟩⟩
      · calc
          (x ^ 2 + z) / 2 = 3 * r ^ 2 := hP
          _ = 12 * a ^ 4 := by rw [hra]; ring
      · calc
          (x ^ 2 - z) / 2 = s ^ 2 := hQ
          _ = b ^ 4 := by rw [hsb]; ring
    · refine ⟨a, b, hab, ht, Or.inr <| Or.inl ⟨?_, ?_⟩⟩
      · calc
          (x ^ 2 + z) / 2 = 3 * r ^ 2 := hP
          _ = 3 * a ^ 4 := by rw [hra]; ring
      · calc
          (x ^ 2 - z) / 2 = s ^ 2 := hQ
          _ = 4 * b ^ 4 := by rw [hsb]; ring
  · have hRootProd : r * s = 2 * (y / 2) ^ 2 := by
      rw [← hRoot, even_sq_div_two (quarticThree_even_y hEq)]
    rcases coprime_mul_eq_prime_mul_sq_split Nat.prime_two hrsCop hRootProd with
        ⟨a, b, hab, hra, hsb, ht⟩ | ⟨a, b, hab, hra, hsb, ht⟩
    · refine ⟨a, b, hab, ht, Or.inr <| Or.inr <| Or.inl ⟨?_, ?_⟩⟩
      · calc
          (x ^ 2 + z) / 2 = r ^ 2 := hP
          _ = 4 * a ^ 4 := by rw [hra]; ring
      · calc
          (x ^ 2 - z) / 2 = 3 * s ^ 2 := hQ
          _ = 3 * b ^ 4 := by rw [hsb]; ring
    · refine ⟨a, b, hab, ht, Or.inr <| Or.inr <| Or.inr ⟨?_, ?_⟩⟩
      · calc
          (x ^ 2 + z) / 2 = r ^ 2 := hP
          _ = a ^ 4 := by rw [hra]; ring
      · calc
          (x ^ 2 - z) / 2 = 3 * s ^ 2 := hQ
          _ = 12 * b ^ 4 := by rw [hsb]; ring

/-! ## Eliminating the two impossible allocations -/

private theorem zmod4_no_odd_square_eq_three_fourth_fourth :
    ∀ x a b : ZMod 4, IsUnit x →
      x ^ 2 ≠ 3 * a ^ 4 + 4 * b ^ 4 := by
  decide

private theorem zmod4_no_odd_square_eq_four_fourth_three_fourth :
    ∀ x a b : ZMod 4, IsUnit x →
      x ^ 2 ≠ 4 * a ^ 4 + 3 * b ^ 4 := by
  decide

private theorem isUnit_zmod4_of_odd {n : ℕ} (hn : Odd n) :
    IsUnit (n : ZMod 4) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 4 = 2 ^ 2 by norm_num] using
    Nat.prime_two.coprime_pow_of_not_dvd hn.not_two_dvd_nat (m := 2)

/-- Witness-rich first-descent data for fixed roots `a,b`.  The half
allocation is retained in addition to the normalized equation and exact
product formula. -/
structure QuarticThreeFirstDescentWitness (x y z a b : ℕ) : Prop where
  coprime : Nat.Coprime a b
  a_pos : 0 < a
  b_pos : 0 < b
  a_odd : Odd a
  square_eq : x ^ 2 = a ^ 4 + 12 * b ^ 4
  y_half_eq : y / 2 = a * b
  y_eq : y = 2 * a * b
  half_allocation :
    (((x ^ 2 + z) / 2 = a ^ 4) ∧
      ((x ^ 2 - z) / 2 = 12 * b ^ 4)) ∨
    (((x ^ 2 + z) / 2 = 12 * b ^ 4) ∧
      ((x ^ 2 - z) / 2 = a ^ 4))

/-- Every primitive positive solution of `x^4 = 3*y^4 + z^2` reaches the
classical first-descent normal form

`x^2 = a^4 + 12*b^4`,  `y/2 = a*b`,  `y = 2*a*b`,

with positive coprime roots and odd `a`. -/
theorem quarticThree_first_descent {x y z : ℕ}
    (hy : y ≠ 0) (hxy : Nat.Coprime x y)
    (hEq : x ^ 4 = 3 * y ^ 4 + z ^ 2) :
    ∃ a b : ℕ, QuarticThreeFirstDescentWitness x y z a b := by
  have hyEven := quarticThree_even_y hEq
  have hxNotEven : ¬Even x := by
    intro hxEven
    exact not_both_even_of_coprime hxy ⟨hxEven, hyEven⟩
  have hxOdd : Odd x := Nat.not_even_iff_odd.mp hxNotEven
  have hSum := quarticThree_halves_sum hy hxy hEq
  obtain ⟨a, b, hab, hHalf, hCases⟩ :=
    quarticThree_four_allocations hy hxy hEq
  have hyDouble : y = 2 * (y / 2) := by
    obtain ⟨k, rfl⟩ := hyEven
    omega
  have normalize
      {a b : ℕ} (hab : Nat.Coprime a b) (hHalf : y / 2 = a * b)
      (hAlloc :
        ((((x ^ 2 + z) / 2 = a ^ 4) ∧
          ((x ^ 2 - z) / 2 = 12 * b ^ 4)) ∨
        (((x ^ 2 + z) / 2 = 12 * b ^ 4) ∧
          ((x ^ 2 - z) / 2 = a ^ 4)))) :
      QuarticThreeFirstDescentWitness x y z a b := by
    have hSquare : x ^ 2 = a ^ 4 + 12 * b ^ 4 := by
      rcases hAlloc with hAlloc | hAlloc
      · rw [← hSum, hAlloc.1, hAlloc.2]
      · rw [← hSum, hAlloc.1, hAlloc.2, add_comm]
    have hyAB : y = 2 * a * b := by
      rw [hyDouble, hHalf]
      ring
    have ha : 0 < a := by
      by_contra ha
      have : a = 0 := by omega
      simp only [this, zero_mul, mul_zero] at hyAB
      exact hy hyAB
    have hb : 0 < b := by
      by_contra hb
      have : b = 0 := by omega
      simp only [this, mul_zero] at hyAB
      exact hy hyAB
    have haOdd : Odd a := by
      have hOddSum : Odd (a ^ 4 + 12 * b ^ 4) := by
        rw [← hSquare]
        exact hxOdd.pow
      have hEvenTerm : Even (12 * b ^ 4) := by
        exact ⟨6 * b ^ 4, by ring⟩
      have ha4Odd : Odd (a ^ 4) :=
        ((Nat.odd_add).mp hOddSum).mpr hEvenTerm
      exact Nat.not_even_iff_odd.mp fun haEven ↦
        (Nat.not_even_iff_odd.mpr ha4Odd) (haEven.pow_of_ne_zero (by norm_num))
    exact ⟨hab, ha, hb, haOdd, hSquare, hHalf, hyAB, hAlloc⟩
  rcases hCases with hFirst | hMiddleOne | hMiddleTwo | hLast
  · exact ⟨b, a, normalize hab.symm (by simpa only [mul_comm] using hHalf)
      (Or.inr ⟨hFirst.1, hFirst.2⟩)⟩
  · exfalso
    have hNat : x ^ 2 = 3 * a ^ 4 + 4 * b ^ 4 := by
      rw [← hSum, hMiddleOne.1, hMiddleOne.2]
    have hCast : (x : ZMod 4) ^ 2 =
        3 * (a : ZMod 4) ^ 4 + 4 * (b : ZMod 4) ^ 4 := by
      simpa only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ ↦ (n : ZMod 4)) hNat
    exact zmod4_no_odd_square_eq_three_fourth_fourth _ _ _
      (isUnit_zmod4_of_odd hxOdd) hCast
  · exfalso
    have hNat : x ^ 2 = 4 * a ^ 4 + 3 * b ^ 4 := by
      rw [← hSum, hMiddleTwo.1, hMiddleTwo.2]
    have hCast : (x : ZMod 4) ^ 2 =
        4 * (a : ZMod 4) ^ 4 + 3 * (b : ZMod 4) ^ 4 := by
      simpa only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ ↦ (n : ZMod 4)) hNat
    exact zmod4_no_odd_square_eq_four_fourth_three_fourth _ _ _
      (isUnit_zmod4_of_odd hxOdd) hCast
  · exact ⟨a, b, normalize hab hHalf (Or.inl ⟨hLast.1, hLast.2⟩)⟩

/-- Projection of `quarticThree_first_descent` to its normalized Diophantine
equation, while retaining positivity, coprimality, parity, and root-product
data. -/
theorem quarticThree_first_descent_normal_form {x y z : ℕ}
    (hy : y ≠ 0) (hxy : Nat.Coprime x y)
    (hEq : x ^ 4 = 3 * y ^ 4 + z ^ 2) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ Odd a ∧
      x ^ 2 = a ^ 4 + 12 * b ^ 4 ∧ y / 2 = a * b ∧ y = 2 * a * b := by
  obtain ⟨a, b, D⟩ := quarticThree_first_descent hy hxy hEq
  exact ⟨a, b, D.a_pos, D.b_pos, D.coprime, D.a_odd,
    D.square_eq, D.y_half_eq, D.y_eq⟩


private theorem zmod8_no_square_eq_quartic_add_twelve_quartic_of_units :
    ∀ x a b : ZMod 8,
      IsUnit a → IsUnit b → x ^ 2 ≠ a ^ 4 + 12 * b ^ 4 := by
  decide

private theorem isUnit_zmod8_of_not_even_second {n : ℕ} (hn : ¬Even n) :
    IsUnit (n : ZMod 8) := by
  rw [ZMod.isUnit_iff_coprime]
  have h2 : ¬2 ∣ n := by simpa only [even_iff_two_dvd] using hn
  simpa only [show 8 = 2 ^ 3 by norm_num] using
    Nat.prime_two.coprime_pow_of_not_dvd h2 (m := 3)

/-- The square base is odd in `x^2 = a^4 + 12*b^4` when `a` is odd. -/
theorem quarticThree_second_x_odd {x a b : ℕ} (ha : Odd a)
    (hEq : x ^ 2 = a ^ 4 + 12 * b ^ 4) : Odd x := by
  have hTwelveEven : Even (12 * b ^ 4) :=
    (by decide : Even (12 : ℕ)).mul_right (b ^ 4)
  have hRhsOdd : Odd (a ^ 4 + 12 * b ^ 4) :=
    ha.pow.add_even hTwelveEven
  have hXSqOdd : Odd (x ^ 2) := by simpa only [hEq] using hRhsOdd
  by_contra hx
  have hxEven : Even x := Nat.not_odd_iff_even.mp hx
  exact (Nat.not_even_iff_odd.mpr hXSqOdd)
    (hxEven.pow_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0))

/-- The fourth-power base `b` is forced even by reduction modulo eight. -/
theorem quarticThree_second_b_even {x a b : ℕ} (ha : Odd a)
    (hEq : x ^ 2 = a ^ 4 + 12 * b ^ 4) : Even b := by
  by_contra hb
  have hEqZ : (x : ZMod 8) ^ 2 =
      (a : ZMod 8) ^ 4 + 12 * (b : ZMod 8) ^ 4 := by
    simpa only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ZMod 8)) hEq
  exact zmod8_no_square_eq_quartic_add_twelve_quartic_of_units _ _ _
    (isUnit_zmod8_of_not_even_second (Nat.not_even_iff_odd.mpr ha))
    (isUnit_zmod8_of_not_even_second hb) hEqZ

/-- Coprimality of the two fourth-power roots propagates to `x` and `a`.
Indeed `gcd(x,a)^2` divides `12` and is odd, forcing it to be one. -/
theorem quarticThree_second_coprime_x_a {x a b : ℕ}
    (hab : Nat.Coprime a b) (ha : Odd a)
    (hEq : x ^ 2 = a ^ 4 + 12 * b ^ 4) : Nat.Coprime x a := by
  let d := Nat.gcd x a
  have hdx : d ∣ x := Nat.gcd_dvd_left x a
  have hda : d ∣ a := Nat.gcd_dvd_right x a
  have hd2x2 : d ^ 2 ∣ x ^ 2 := by
    obtain ⟨u, hu⟩ := hdx
    use u ^ 2
    rw [hu]
    ring
  have hd2a4 : d ^ 2 ∣ a ^ 4 := by
    obtain ⟨v, hv⟩ := hda
    use d ^ 2 * v ^ 4
    rw [hv]
    ring
  have ha4le : a ^ 4 ≤ x ^ 2 := by omega
  have hdiff : x ^ 2 - a ^ 4 = 12 * b ^ 4 := by omega
  have hd2TwelveB : d ^ 2 ∣ 12 * b ^ 4 := by
    rw [← hdiff]
    exact Nat.dvd_sub hd2x2 hd2a4
  have hdB : Nat.Coprime d b :=
    Nat.Coprime.of_dvd_left hda hab
  have hd2B4 : Nat.Coprime (d ^ 2) (b ^ 4) := hdB.pow 2 4
  have hd2Twelve : d ^ 2 ∣ 12 :=
    hd2B4.dvd_of_dvd_mul_right hd2TwelveB
  have hdNotEven : ¬Even d := by
    intro hdEven
    exact (Nat.not_even_iff_odd.mpr ha) (hdEven.trans_dvd hda)
  have hdne : d ≠ 0 := by
    intro hd
    simp only [hd, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_dvd_iff] at hd2Twelve
    omega
  have hdle : d ^ 2 ≤ 12 := Nat.le_of_dvd (by norm_num) hd2Twelve
  have hdleThree : d ≤ 3 := by nlinarith
  have hdOne : d = 1 := by
    interval_cases d
    · exact (hdne rfl).elim
    · rfl
    · exact (hdNotEven (by norm_num)).elim
    · norm_num at hd2Twelve
  exact Nat.coprime_iff_gcd_eq_one.mpr hdOne

/-- Positivity of `b` makes `a^2` strictly smaller than `x`. -/
theorem quarticThree_second_a_sq_lt_x {x a b : ℕ} (hb : b ≠ 0)
    (hEq : x ^ 2 = a ^ 4 + 12 * b ^ 4) : a ^ 2 < x := by
  have hterm : 0 < 12 * b ^ 4 := by positivity
  have hpow : a ^ 4 < x ^ 2 := by omega
  have hpow' : (a ^ 2) ^ 2 < x ^ 2 := by
    simpa only [show a ^ 4 = (a ^ 2) ^ 2 by ring] using hpow
  exact (Nat.pow_lt_pow_iff_left (n := 2) (by norm_num)).mp hpow'

/-- Difference-of-squares product at the second descent stage. -/
theorem quarticThree_second_factor_product {x a b : ℕ}
    (hEq : x ^ 2 = a ^ 4 + 12 * b ^ 4) :
    (x + a ^ 2) * (x - a ^ 2) = 12 * b ^ 4 := by
  have hdiff : x ^ 2 - a ^ 4 = 12 * b ^ 4 := by omega
  calc
    (x + a ^ 2) * (x - a ^ 2) = x ^ 2 - (a ^ 2) ^ 2 :=
      (Nat.sq_sub_sq x (a ^ 2)).symm
    _ = x ^ 2 - a ^ 4 := by ring_nf
    _ = 12 * b ^ 4 := hdiff

/-- The two second-stage factors have gcd exactly two. -/
theorem quarticThree_second_factor_gcd_eq_two {x a b : ℕ}
    (hb : b ≠ 0) (hab : Nat.Coprime a b) (ha : Odd a)
    (hEq : x ^ 2 = a ^ 4 + 12 * b ^ 4) :
    Nat.gcd (x + a ^ 2) (x - a ^ 2) = 2 := by
  have hxOdd : Odd x := quarticThree_second_x_odd ha hEq
  have hxa : Nat.Coprime x a :=
    quarticThree_second_coprime_x_a hab ha hEq
  have hxa2 : Nat.Coprime x (a ^ 2) := hxa.pow_right 2
  have hAddA2 : Nat.Coprime (x + a ^ 2) (a ^ 2) :=
    Nat.coprime_add_self_left.mpr hxa2
  let d := Nat.gcd (x + a ^ 2) (x - a ^ 2)
  have hdAdd : d ∣ x + a ^ 2 := Nat.gcd_dvd_left _ _
  have hdSub : d ∣ x - a ^ 2 := Nat.gcd_dvd_right _ _
  have hale : a ^ 2 ≤ x := (quarticThree_second_a_sq_lt_x hb hEq).le
  have hTwoA2 : (x + a ^ 2) - (x - a ^ 2) = 2 * a ^ 2 := by omega
  have hdTwoA2 : d ∣ 2 * a ^ 2 := by
    simpa only [hTwoA2] using Nat.dvd_sub hdAdd hdSub
  have hdCopA2 : Nat.Coprime d (a ^ 2) :=
    Nat.Coprime.of_dvd_left hdAdd hAddA2
  have hdTwo : d ∣ 2 := hdCopA2.dvd_of_dvd_mul_right hdTwoA2
  have hAddEven : Even (x + a ^ 2) := hxOdd.add_odd ha.pow
  have hSubEven : Even (x - a ^ 2) := hxOdd.tsub_odd ha.pow
  have hTwoD : 2 ∣ d := Nat.dvd_gcd
    (even_iff_two_dvd.mp hAddEven) (even_iff_two_dvd.mp hSubEven)
  exact Nat.dvd_antisymm hdTwo hTwoD

/-- Dividing the exact common factor two makes the second-stage factors
coprime. -/
theorem quarticThree_second_halves_coprime {x a b : ℕ}
    (hb : b ≠ 0) (hab : Nat.Coprime a b) (ha : Odd a)
    (hEq : x ^ 2 = a ^ 4 + 12 * b ^ 4) :
    Nat.Coprime ((x + a ^ 2) / 2) ((x - a ^ 2) / 2) := by
  have hgcd := quarticThree_second_factor_gcd_eq_two hb hab ha hEq
  have h := Nat.coprime_div_gcd_div_gcd
    (m := x + a ^ 2) (n := x - a ^ 2) (by simp [hgcd])
  simpa only [hgcd] using h

/-- Exact product of the coprime second-stage halves. -/
theorem quarticThree_second_halves_product {x a b : ℕ} (ha : Odd a)
    (hEq : x ^ 2 = a ^ 4 + 12 * b ^ 4) :
    ((x + a ^ 2) / 2) * ((x - a ^ 2) / 2) = 3 * b ^ 4 := by
  have hxOdd : Odd x := quarticThree_second_x_odd ha hEq
  have hAddEven : Even (x + a ^ 2) := hxOdd.add_odd ha.pow
  have ha2le : a ^ 2 ≤ x := by
    have hpow : a ^ 4 ≤ x ^ 2 := by omega
    have hpow' : (a ^ 2) ^ 2 ≤ x ^ 2 := by
      simpa only [show a ^ 4 = (a ^ 2) ^ 2 by ring] using hpow
    exact (Nat.pow_le_pow_iff_left (n := 2) (by norm_num)).mp hpow'
  have hSubEven : Even (x - a ^ 2) := hxOdd.tsub_odd ha.pow
  have hAddSplit : 2 * ((x + a ^ 2) / 2) = x + a ^ 2 :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp hAddEven)
  have hSubSplit : 2 * ((x - a ^ 2) / 2) = x - a ^ 2 :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp hSubEven)
  have hRaw := quarticThree_second_factor_product hEq
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4)
  calc
    4 * (((x + a ^ 2) / 2) * ((x - a ^ 2) / 2)) =
        (2 * ((x + a ^ 2) / 2)) * (2 * ((x - a ^ 2) / 2)) := by ring
    _ = (x + a ^ 2) * (x - a ^ 2) := by rw [hAddSplit, hSubSplit]
    _ = 12 * b ^ 4 := hRaw
    _ = 4 * (3 * b ^ 4) := by ring


/-! ## Difference of the coprime halves -/

/-- The two second-stage halves differ by exactly `a^2`. -/
theorem quarticThree_second_halves_difference {x a b : ℕ}
    (hb : b ≠ 0) (ha : Odd a)
    (hEq : x ^ 2 = a ^ 4 + 12 * b ^ 4) :
    (x + a ^ 2) / 2 = (x - a ^ 2) / 2 + a ^ 2 := by
  have hxOdd := quarticThree_second_x_odd ha hEq
  have ha2le : a ^ 2 ≤ x := (quarticThree_second_a_sq_lt_x hb hEq).le
  have hAddEven : Even (x + a ^ 2) := hxOdd.add_odd ha.pow
  have hSubEven : Even (x - a ^ 2) := hxOdd.tsub_odd ha.pow
  have hAddSplit : 2 * ((x + a ^ 2) / 2) = x + a ^ 2 :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp hAddEven)
  have hSubSplit : 2 * ((x - a ^ 2) / 2) = x - a ^ 2 :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp hSubEven)
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
  rw [hAddSplit, Nat.mul_add, hSubSplit]
  omega

/-! ## The exhaustive four-way allocation -/

/-- Before congruence elimination, the second split has exactly four
allocations.  The witnesses are positive and coprime, and their exact product
is the original fourth-power root `b`. -/
theorem quarticThree_second_four_allocations {x a b : ℕ}
    (hb : b ≠ 0) (hab : Nat.Coprime a b) (ha : Odd a)
    (hEq : x ^ 2 = a ^ 4 + 12 * b ^ 4) :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧ Nat.Coprime c d ∧ b = c * d ∧
      ((Even c ∧ Odd d ∧
          (x + a ^ 2) / 2 = 3 * c ^ 4 ∧
          (x - a ^ 2) / 2 = d ^ 4) ∨
       (Odd c ∧ Even d ∧
          (x + a ^ 2) / 2 = 3 * c ^ 4 ∧
          (x - a ^ 2) / 2 = d ^ 4) ∨
       (Even c ∧ Odd d ∧
          (x + a ^ 2) / 2 = c ^ 4 ∧
          (x - a ^ 2) / 2 = 3 * d ^ 4) ∨
       (Odd c ∧ Even d ∧
          (x + a ^ 2) / 2 = c ^ 4 ∧
          (x - a ^ 2) / 2 = 3 * d ^ 4)) := by
  have hCop := quarticThree_second_halves_coprime hb hab ha hEq
  have hProd := quarticThree_second_halves_product ha hEq
  have hProdSq :
      ((x + a ^ 2) / 2) * ((x - a ^ 2) / 2) =
        3 * (b ^ 2) ^ 2 := by
    simpa only [show b ^ 4 = (b ^ 2) ^ 2 by ring] using hProd
  have hbEven := quarticThree_second_b_even ha hEq
  rcases coprime_mul_eq_prime_mul_sq_split Nat.prime_three hCop hProdSq with
      ⟨r, s, hrs, hUpper, hLower, hRoot⟩ |
      ⟨r, s, hrs, hUpper, hLower, hRoot⟩
  · obtain ⟨c, d, hcd, hr, hs, hbRoot⟩ :=
      coprime_mul_eq_sq_split hrs hRoot.symm
    have hcpos : 0 < c := by
      by_contra hc
      have hc0 : c = 0 := by omega
      rw [hc0, zero_mul] at hbRoot
      exact hb hbRoot
    have hdpos : 0 < d := by
      by_contra hd
      have hd0 : d = 0 := by omega
      rw [hd0, mul_zero] at hbRoot
      exact hb hbRoot
    have hUpper' : (x + a ^ 2) / 2 = 3 * c ^ 4 := by
      calc
        (x + a ^ 2) / 2 = 3 * r ^ 2 := hUpper
        _ = 3 * c ^ 4 := by rw [hr]; ring
    have hLower' : (x - a ^ 2) / 2 = d ^ 4 := by
      calc
        (x - a ^ 2) / 2 = s ^ 2 := hLower
        _ = d ^ 4 := by rw [hs]; ring
    have hEvenProd : Even (c * d) := by simpa only [← hbRoot] using hbEven
    rcases Nat.even_mul.mp hEvenProd with hcEven | hdEven
    · have hdOdd : Odd d := Nat.not_even_iff_odd.mp fun hdEven ↦
        not_both_even_of_coprime hcd ⟨hcEven, hdEven⟩
      exact ⟨c, d, hcpos, hdpos, hcd, hbRoot,
        Or.inl ⟨hcEven, hdOdd, hUpper', hLower'⟩⟩
    · have hcOdd : Odd c := Nat.not_even_iff_odd.mp fun hcEven ↦
        not_both_even_of_coprime hcd ⟨hcEven, hdEven⟩
      exact ⟨c, d, hcpos, hdpos, hcd, hbRoot,
        Or.inr <| Or.inl ⟨hcOdd, hdEven, hUpper', hLower'⟩⟩
  · obtain ⟨c, d, hcd, hr, hs, hbRoot⟩ :=
      coprime_mul_eq_sq_split hrs hRoot.symm
    have hcpos : 0 < c := by
      by_contra hc
      have hc0 : c = 0 := by omega
      rw [hc0, zero_mul] at hbRoot
      exact hb hbRoot
    have hdpos : 0 < d := by
      by_contra hd
      have hd0 : d = 0 := by omega
      rw [hd0, mul_zero] at hbRoot
      exact hb hbRoot
    have hUpper' : (x + a ^ 2) / 2 = c ^ 4 := by
      calc
        (x + a ^ 2) / 2 = r ^ 2 := hUpper
        _ = c ^ 4 := by rw [hr]; ring
    have hLower' : (x - a ^ 2) / 2 = 3 * d ^ 4 := by
      calc
        (x - a ^ 2) / 2 = 3 * s ^ 2 := hLower
        _ = 3 * d ^ 4 := by rw [hs]; ring
    have hEvenProd : Even (c * d) := by simpa only [← hbRoot] using hbEven
    rcases Nat.even_mul.mp hEvenProd with hcEven | hdEven
    · have hdOdd : Odd d := Nat.not_even_iff_odd.mp fun hdEven ↦
        not_both_even_of_coprime hcd ⟨hcEven, hdEven⟩
      exact ⟨c, d, hcpos, hdpos, hcd, hbRoot,
        Or.inr <| Or.inr <| Or.inl
          ⟨hcEven, hdOdd, hUpper', hLower'⟩⟩
    · have hcOdd : Odd c := Nat.not_even_iff_odd.mp fun hcEven ↦
        not_both_even_of_coprime hcd ⟨hcEven, hdEven⟩
      exact ⟨c, d, hcpos, hdpos, hcd, hbRoot,
        Or.inr <| Or.inr <| Or.inr
          ⟨hcOdd, hdEven, hUpper', hLower'⟩⟩

/-! ## Modulo-sixteen elimination -/

private theorem isUnit_zmod16_of_odd_second_split {n : ℕ} (hn : Odd n) :
    IsUnit (n : ZMod 16) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 16 = 2 ^ 4 by norm_num] using
    Nat.prime_two.coprime_pow_of_not_dvd hn.not_two_dvd_nat (m := 4)

private theorem zmod16_no_three_even_fourth_eq_odd_fourth_add_odd_square :
    ∀ k d a : ZMod 16, IsUnit d → IsUnit a →
      3 * (k + k) ^ 4 ≠ d ^ 4 + a ^ 2 := by
  decide

private theorem zmod16_no_three_odd_fourth_eq_even_fourth_add_odd_square :
    ∀ c k a : ZMod 16, IsUnit c → IsUnit a →
      3 * c ^ 4 ≠ (k + k) ^ 4 + a ^ 2 := by
  decide

private theorem zmod16_no_even_fourth_eq_three_odd_fourth_add_odd_square :
    ∀ k d a : ZMod 16, IsUnit d → IsUnit a →
      (k + k) ^ 4 ≠ 3 * d ^ 4 + a ^ 2 := by
  decide

/-- Witness-rich data for the unique second-stage allocation which survives
modulo sixteen.  The even fourth-power root is exposed as `2*d`, so the
structure itself contains the next primitive quartic-three equation and the
exact root product needed for the strict descent. -/
structure QuarticThreeSecondFactorSplit (x a b : ℕ) where
  c : ℕ
  d : ℕ
  c_pos : 0 < c
  d_pos : 0 < d
  coprime_c_two_d : Nat.Coprime c (2 * d)
  c_odd : Odd c
  b_eq : b = c * (2 * d)
  upper_half : (x + a ^ 2) / 2 = c ^ 4
  lower_half : (x - a ^ 2) / 2 = 3 * (2 * d) ^ 4
  equation : c ^ 4 = 3 * (2 * d) ^ 4 + a ^ 2

/-- Of the four raw allocations, only

`(x+a^2)/2 = c^4`, `(x-a^2)/2 = 3*(2*d)^4`

survives.  In particular, it produces another positive primitive
quartic-three equation and retains `b = c*(2*d)`. -/
theorem quarticThree_second_factor_split {x a b : ℕ}
    (hb : b ≠ 0) (hab : Nat.Coprime a b) (ha : Odd a)
    (hEq : x ^ 2 = a ^ 4 + 12 * b ^ 4) :
    Nonempty (QuarticThreeSecondFactorSplit x a b) := by
  have hDiff := quarticThree_second_halves_difference hb ha hEq
  obtain ⟨c, d, hcpos, hdpos, hcd, hbRoot, hCases⟩ :=
    quarticThree_second_four_allocations hb hab ha hEq
  rcases hCases with hCase | hCase | hCase | hCase
  · rcases hCase with ⟨hcEven, hdOdd, hUpper, hLower⟩
    have hNat : 3 * c ^ 4 = d ^ 4 + a ^ 2 := by
      simpa only [hUpper, hLower] using hDiff
    obtain ⟨k, hk⟩ := hcEven
    have hNat' : 3 * (k + k) ^ 4 = d ^ 4 + a ^ 2 := by
      simpa only [hk] using hNat
    have hCast : 3 * ((k : ZMod 16) + k) ^ 4 =
        (d : ZMod 16) ^ 4 + (a : ZMod 16) ^ 2 := by
      simpa only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ ↦ (n : ZMod 16)) hNat'
    exact ((zmod16_no_three_even_fourth_eq_odd_fourth_add_odd_square _ _ _
      (isUnit_zmod16_of_odd_second_split hdOdd)
      (isUnit_zmod16_of_odd_second_split ha)) hCast).elim
  · rcases hCase with ⟨hcOdd, hdEven, hUpper, hLower⟩
    have hNat : 3 * c ^ 4 = d ^ 4 + a ^ 2 := by
      simpa only [hUpper, hLower] using hDiff
    obtain ⟨k, hk⟩ := hdEven
    have hNat' : 3 * c ^ 4 = (k + k) ^ 4 + a ^ 2 := by
      simpa only [hk] using hNat
    have hCast : 3 * (c : ZMod 16) ^ 4 =
        ((k : ZMod 16) + k) ^ 4 + (a : ZMod 16) ^ 2 := by
      simpa only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ ↦ (n : ZMod 16)) hNat'
    exact ((zmod16_no_three_odd_fourth_eq_even_fourth_add_odd_square _ _ _
      (isUnit_zmod16_of_odd_second_split hcOdd)
      (isUnit_zmod16_of_odd_second_split ha)) hCast).elim
  · rcases hCase with ⟨hcEven, hdOdd, hUpper, hLower⟩
    have hNat : c ^ 4 = 3 * d ^ 4 + a ^ 2 := by
      simpa only [hUpper, hLower] using hDiff
    obtain ⟨k, hk⟩ := hcEven
    have hNat' : (k + k) ^ 4 = 3 * d ^ 4 + a ^ 2 := by
      simpa only [hk] using hNat
    have hCast : ((k : ZMod 16) + k) ^ 4 =
        3 * (d : ZMod 16) ^ 4 + (a : ZMod 16) ^ 2 := by
      simpa only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ ↦ (n : ZMod 16)) hNat'
    exact ((zmod16_no_even_fourth_eq_three_odd_fourth_add_odd_square _ _ _
      (isUnit_zmod16_of_odd_second_split hdOdd)
      (isUnit_zmod16_of_odd_second_split ha)) hCast).elim
  · rcases hCase with ⟨hcOdd, hdEven, hUpper, hLower⟩
    obtain ⟨d', hd'⟩ := hdEven
    have hdEq : d = 2 * d' := by omega
    have hd'pos : 0 < d' := by omega
    have hCop : Nat.Coprime c (2 * d') := by simpa only [← hdEq] using hcd
    have hbEq : b = c * (2 * d') := by simpa only [← hdEq] using hbRoot
    have hLower' : (x - a ^ 2) / 2 = 3 * (2 * d') ^ 4 := by
      simpa only [← hdEq] using hLower
    have hEquation : c ^ 4 = 3 * (2 * d') ^ 4 + a ^ 2 := by
      simpa only [hUpper, hLower'] using hDiff
    exact ⟨⟨c, d', hcpos, hd'pos, hCop, hcOdd, hbEq,
      hUpper, hLower', hEquation⟩⟩

/-! ## Strict size data for the next descent -/

/-- The new even fourth-power root is no larger than the old root `b`.
Together with a first-stage identity `y = 2*a*b`, this is enough to obtain
the strict inequality needed for infinite descent. -/
theorem QuarticThreeSecondFactorSplit.two_d_le_b {x a b : ℕ}
    (D : QuarticThreeSecondFactorSplit x a b) : 2 * D.d ≤ b := by
  calc
    2 * D.d ≤ D.c * (2 * D.d) :=
      Nat.le_mul_of_pos_left (2 * D.d) D.c_pos
    _ = b := D.b_eq.symm

/-- Linking the exact second-stage root product with the first-stage
`y = 2*a*b` proves that the new positive root `2*d` is strictly smaller than
the original descent parameter `y`. -/
theorem QuarticThreeSecondFactorSplit.two_d_lt_original_y {x a b y : ℕ}
    (D : QuarticThreeSecondFactorSplit x a b) (ha : 0 < a)
    (hy : y = 2 * a * b) : 0 < 2 * D.d ∧ 2 * D.d < y := by
  constructor
  · exact Nat.mul_pos (by norm_num) D.d_pos
  · apply lt_of_le_of_lt D.two_d_le_b
    have hbpos : 0 < b := by
      calc
        0 < D.c * (2 * D.d) :=
          Nat.mul_pos D.c_pos (Nat.mul_pos (by norm_num) D.d_pos)
        _ = b := D.b_eq.symm
    calc
      b < 2 * b := by omega
      _ ≤ (2 * a) * b :=
        Nat.mul_le_mul_right b (Nat.mul_le_mul_left 2 ha)
      _ = 2 * a * b := by ring
      _ = y := hy.symm



/-- Every primitive auxiliary solution gives one with smaller second quartic base. -/
theorem PrimitiveQuarticThreeData.exists_smaller
    (D : PrimitiveQuarticThreeData) :
    ∃ E : PrimitiveQuarticThreeData, E.y < D.y := by
  obtain ⟨a, b, D₁⟩ :=
    quarticThree_first_descent D.y_ne_zero D.coprime_xy D.equation
  obtain ⟨D₂⟩ := quarticThree_second_factor_split
    (ne_of_gt D₁.b_pos) D₁.coprime D₁.a_odd D₁.square_eq
  have hSize := D₂.two_d_lt_original_y D₁.a_pos D₁.y_eq
  refine ⟨{
    x := D₂.c
    y := 2 * D₂.d
    q := a
    x_ne_zero := ne_of_gt D₂.c_pos
    y_ne_zero := ne_of_gt hSize.1
    coprime_xy := D₂.coprime_c_two_d
    equation := D₂.equation
  }, hSize.2⟩

/-- No primitive natural solution with nonzero quartic bases exists. -/
theorem PrimitiveQuarticThreeData.false (D : PrimitiveQuarticThreeData) :
    False := by
  let P : ℕ → Prop := fun n ↦
    ∀ E : PrimitiveQuarticThreeData, E.y = n → False
  have hP : ∀ n : ℕ, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro E hEn
        obtain ⟨F, hFE⟩ := E.exists_smaller
        exact ih F.y (by simpa only [hEn] using hFE) F rfl
  exact hP D.y D rfl

/-- Direct theorem boundary for integration after the Gaussian reduction. -/
theorem no_primitive_quartic_three
    {u v w : ℕ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : Nat.Coprime u v)
    (hEq : u ^ 4 = 3 * v ^ 4 + w ^ 2) : False := by
  exact (PrimitiveQuarticThreeData.mk u v w hu hv huv hEq).false

end BealRegular.QuarticThreeDescent
