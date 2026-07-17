import BealRegular.GaussianCubeParametrization
import BealRegular.QuarticThreeDescent
import BealRegular.SignatureReduction

/-!
# Exact Beal conclusion for the reduced signature `(4, 4, 3)`

This module connects the Gaussian-cube coordinate parametrization to the
quartic-three infinite descent.  It proves both the primitive nonexistence
statement and the exact Beal conclusion: every nonzero natural solution of

`A ^ 4 + B ^ 4 = C ^ 3`

has a prime dividing all three bases.
-/

namespace BealRegular.GaussianQuarticThreeBridge

open BealRegular.GaussianCubeParametrization
open BealRegular.QuarticThreeDescent
open BealRegular.SignatureReduction

private theorem zmod16_no_odd_odd_fourth_sum_cube :
    ∀ x y z : ZMod 16, IsUnit x → IsUnit y → x ^ 4 + y ^ 4 ≠ z ^ 3 := by
  decide

private theorem isUnit_zmod16_of_not_even {n : ℕ} (hn : ¬Even n) :
    IsUnit (n : ZMod 16) := by
  rw [ZMod.isUnit_iff_coprime]
  have h2 : ¬2 ∣ n := by simpa only [even_iff_two_dvd] using hn
  simpa only [show 16 = 2 ^ 4 by norm_num] using
    Nat.prime_two.coprime_pow_of_not_dvd h2 (m := 4)

/-- A primitive `(4,4,3)` equation necessarily has odd left-hand side. -/
theorem fourth_sum_odd_of_coprime_eq_cube {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hEq : A ^ 4 + B ^ 4 = C ^ 3) :
    Odd (A ^ 4 + B ^ 4) := by
  apply Nat.not_even_iff_odd.mp
  intro hEven
  have hParity : Even A ↔ Even B := by
    have h := (Nat.even_add.mp hEven)
    simpa only [Nat.even_pow' (by norm_num : (4 : ℕ) ≠ 0)] using h
  by_cases hA : Even A
  · exact not_both_even_of_coprime hAB ⟨hA, hParity.mp hA⟩
  · have hB : ¬Even B := fun hB ↦ hA (hParity.mpr hB)
    have hEqZ : (A : ZMod 16) ^ 4 + (B : ZMod 16) ^ 4 =
        (C : ZMod 16) ^ 3 := by
      simpa only [Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ ↦ (n : ZMod 16)) hEq
    exact zmod16_no_odd_odd_fourth_sum_cube _ _ _
      (isUnit_zmod16_of_not_even hA) (isUnit_zmod16_of_not_even hB) hEqZ

/-! ## Square-product splitting at the exceptional prime three -/

def RegularSquareSplit (u v w : ℕ) : Prop :=
  ∃ r s : ℕ,
    u = r ^ 2 ∧ v = s ^ 2 ∧ w = r * s ∧ Nat.Coprime r s

def ExceptionalThreeSquareSplit (u v w : ℕ) : Prop :=
  ∃ r s : ℕ,
    u = 3 * r ^ 2 ∧ v = 3 * s ^ 2 ∧ w = 3 * r * s ∧
      Nat.Coprime r s ∧ ¬3 ∣ s

/-- Specialized redistribution of a single shared factor three. -/
private theorem primeOverlapSquareSplitAtThree
    {u v w : ℕ} (hgcd : Nat.gcd u v = 3)
    (h3v : 3 ∣ v) (h9v : ¬9 ∣ v) (hpow : u * v = w ^ 2) :
    ExceptionalThreeSquareSplit u v w := by
  have hv_split : 3 * (v / 3) = v := Nat.mul_div_cancel' h3v
  have hcop : Nat.Coprime (3 * u) (v / 3) := by
    refine Nat.coprime_of_dvd ?_
    intro p hp hp3u hpv3
    have hpv : p ∣ v := by
      rw [← hv_split]
      exact dvd_mul_of_dvd_right hpv3 3
    have hp3 : p ∣ 3 := by
      rcases hp.dvd_mul.mp hp3u with hp3 | hpu
      · exact hp3
      · have hpgcd : p ∣ Nat.gcd u v := Nat.dvd_gcd hpu hpv
        simpa only [hgcd] using hpgcd
    have hp_eq_three : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
    subst p
    exfalso
    apply h9v
    have h33 : 3 * 3 ∣ 3 * (v / 3) := mul_dvd_mul_left 3 hpv3
    rw [hv_split] at h33
    simpa only [show 9 = 3 * 3 by norm_num] using h33
  have hredistributed : (3 * u) * (v / 3) = w ^ 2 := by
    calc
      (3 * u) * (v / 3) = u * (3 * (v / 3)) := by ring
      _ = u * v := by rw [hv_split]
      _ = w ^ 2 := hpow
  obtain ⟨R, s, hRsCop, hR, hs, hw⟩ :=
    coprime_mul_eq_sq_split hcop hredistributed
  have h3Rpow : 3 ∣ R ^ 2 := by
    rw [← hR]
    exact dvd_mul_right 3 u
  have h3R : 3 ∣ R := Nat.prime_three.dvd_of_dvd_pow h3Rpow
  obtain ⟨r, hr⟩ := h3R
  have huForm : u = 3 * r ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3)
    calc
      3 * u = R ^ 2 := hR
      _ = (3 * r) ^ 2 := by rw [hr]
      _ = 3 * (3 * r ^ 2) := by ring
  have hvForm : v = 3 * s ^ 2 := by
    calc
      v = 3 * (v / 3) := hv_split.symm
      _ = 3 * s ^ 2 := by rw [hs]
  have hwForm : w = 3 * r * s := by
    calc
      w = R * s := hw
      _ = (3 * r) * s := by rw [hr]
      _ = 3 * r * s := rfl
  have hrsCop : Nat.Coprime r s :=
    Nat.Coprime.of_dvd_left (by rw [hr]; exact dvd_mul_left r 3) hRsCop
  have h3sCop : Nat.Coprime 3 s :=
    Nat.Coprime.of_dvd_left (by rw [hr]; exact dvd_mul_right 3 r) hRsCop
  exact ⟨r, s, huForm, hvForm, hwForm, hrsCop,
    Nat.prime_three.coprime_iff_not_dvd.mp h3sCop⟩

/-- A square product with gcd dividing three has the regular or exceptional
normal form, provided the second factor has only one three in the exceptional
branch. -/
theorem squareProductSplitAtThree
    {u v w : ℕ} (hgcdDvd : Nat.gcd u v ∣ 3)
    (hexact : Nat.gcd u v = 3 → ¬9 ∣ v)
    (hpow : u * v = w ^ 2) :
    RegularSquareSplit u v w ∨ ExceptionalThreeSquareSplit u v w := by
  rcases (Nat.dvd_prime Nat.prime_three).mp hgcdDvd with hgcd | hgcd
  · left
    have hcop : Nat.Coprime u v := Nat.coprime_iff_gcd_eq_one.mpr hgcd
    obtain ⟨r, s, hrs, hu, hv, hw⟩ :=
      coprime_mul_eq_sq_split hcop hpow
    exact ⟨r, s, hu, hv, hw, hrs⟩
  · right
    have h3v : 3 ∣ v := by simpa only [hgcd] using Nat.gcd_dvd_right u v
    exact primeOverlapSquareSplitAtThree hgcd h3v (hexact hgcd) hpow

/-! ## Gcd control for the two cubic-coordinate equations -/

theorem gcd_natAbs_sq_sub_mul_sq_dvd
    {a b : ℤ} {k : ℕ} (hab : Nat.Coprime a.natAbs b.natAbs) :
    Nat.gcd a.natAbs (a * a - (k : ℤ) * b * b).natAbs ∣ k := by
  let g := Nat.gcd a.natAbs (a * a - (k : ℤ) * b * b).natAbs
  have hgaNat : g ∣ a.natAbs := Nat.gcd_dvd_left _ _
  have hgfNat : g ∣ (a * a - (k : ℤ) * b * b).natAbs :=
    Nat.gcd_dvd_right _ _
  have hga : (g : ℤ) ∣ a := Int.natCast_dvd.mpr hgaNat
  have hgf : (g : ℤ) ∣ a * a - (k : ℤ) * b * b :=
    Int.natCast_dvd.mpr hgfNat
  have hgkbb : (g : ℤ) ∣ (k : ℤ) * b * b := by
    have hgaa : (g : ℤ) ∣ a * a := dvd_mul_of_dvd_left hga a
    have hSub := dvd_sub hgaa hgf
    convert hSub using 1
    · rfl
    · ring
  have hgkbbNat : g ∣ k * b.natAbs * b.natAbs := by
    have := Int.natCast_dvd.mp hgkbb
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using this
  have hgb : Nat.Coprime g b.natAbs :=
    Nat.Coprime.of_dvd_left hgaNat hab
  have hgkb : g ∣ k * b.natAbs := by
    apply hgb.dvd_of_dvd_mul_right
    simpa only [mul_assoc] using hgkbbNat
  exact hgb.dvd_of_dvd_mul_right hgkb

theorem re_factor_gcd_dvd_three {a b : ℤ}
    (hcop : Nat.Coprime a.natAbs b.natAbs) :
    Nat.gcd a.natAbs (a * a - 3 * b * b).natAbs ∣ 3 := by
  simpa using (gcd_natAbs_sq_sub_mul_sq_dvd (k := 3) hcop)

theorem im_factor_gcd_dvd_three {a b : ℤ}
    (hcop : Nat.Coprime a.natAbs b.natAbs) :
    Nat.gcd b.natAbs (3 * a * a - b * b).natAbs ∣ 3 := by
  have h := gcd_natAbs_sq_sub_mul_sq_dvd (k := 3) hcop.symm
  have hAbs : (3 * a * a - b * b).natAbs =
      (b * b - 3 * a * a).natAbs := by
    rw [← Int.natAbs_neg]
    congr 1
    ring
  rw [hAbs]
  exact h

theorem re_factor_gcd_eq_three_iff {a b : ℤ}
    (hcop : Nat.Coprime a.natAbs b.natAbs) :
    Nat.gcd a.natAbs (a * a - 3 * b * b).natAbs = 3 ↔ 3 ∣ a.natAbs := by
  let f := a * a - 3 * b * b
  have hgDvd : Nat.gcd a.natAbs f.natAbs ∣ 3 := re_factor_gcd_dvd_three hcop
  constructor
  · intro hg
    have hDvd := Nat.gcd_dvd_left a.natAbs f.natAbs
    rw [hg] at hDvd
    exact hDvd
  · intro h3a
    have h3aInt : (3 : ℤ) ∣ a := Int.natCast_dvd.mpr h3a
    have h3fInt : (3 : ℤ) ∣ f := by
      have haa : (3 : ℤ) ∣ a * a := dvd_mul_of_dvd_left h3aInt a
      have hbb : (3 : ℤ) ∣ 3 * b * b := by
        simpa only [mul_assoc] using dvd_mul_right 3 (b * b)
      exact dvd_sub haa hbb
    have h3f : 3 ∣ f.natAbs := Int.natCast_dvd.mp h3fInt
    exact Nat.dvd_antisymm hgDvd (Nat.dvd_gcd h3a h3f)

theorem im_factor_gcd_eq_three_iff {a b : ℤ}
    (hcop : Nat.Coprime a.natAbs b.natAbs) :
    Nat.gcd b.natAbs (3 * a * a - b * b).natAbs = 3 ↔ 3 ∣ b.natAbs := by
  have h := re_factor_gcd_eq_three_iff (a := b) (b := a) hcop.symm
  have hAbs : (3 * a * a - b * b).natAbs =
      (b * b - 3 * a * a).natAbs := by
    rw [← Int.natAbs_neg]
    congr 1
    ring
  rw [hAbs]
  exact h

theorem re_factor_not_nine_dvd {a b : ℤ}
    (hcop : Nat.Coprime a.natAbs b.natAbs) (h3a : 3 ∣ a.natAbs) :
    ¬9 ∣ (a * a - 3 * b * b).natAbs := by
  intro h9f
  have hCoprime3b : Nat.Coprime 3 b.natAbs :=
    Nat.Coprime.of_dvd_left h3a hcop
  have hNot3b : ¬3 ∣ b.natAbs :=
    Nat.prime_three.coprime_iff_not_dvd.mp hCoprime3b
  have h3aInt : (3 : ℤ) ∣ a := Int.natCast_dvd.mpr h3a
  obtain ⟨r, hr⟩ := h3aInt
  have h9fInt : (9 : ℤ) ∣ a * a - 3 * b * b := Int.natCast_dvd.mpr h9f
  have h9aa : (9 : ℤ) ∣ a * a := by
    refine ⟨r * r, ?_⟩
    rw [hr]
    ring
  have h9threebb : (9 : ℤ) ∣ 3 * b * b := by
    have hSub := dvd_sub h9aa h9fInt
    convert hSub using 1
    · rfl
    · ring
  have h9threebbNat : 9 ∣ 3 * b.natAbs * b.natAbs := by
    have := Int.natCast_dvd.mp h9threebb
    norm_num [Int.natAbs_mul] at this ⊢
    exact this
  have h3bb : 3 ∣ b.natAbs * b.natAbs := by
    apply (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)).mp
    norm_num [mul_assoc] at h9threebbNat ⊢
    exact h9threebbNat
  rcases Nat.prime_three.dvd_mul.mp h3bb with h3b | h3b
  · exact hNot3b h3b
  · exact hNot3b h3b

theorem im_factor_not_nine_dvd {a b : ℤ}
    (hcop : Nat.Coprime a.natAbs b.natAbs) (h3b : 3 ∣ b.natAbs) :
    ¬9 ∣ (3 * a * a - b * b).natAbs := by
  have h := re_factor_not_nine_dvd (a := b) (b := a) hcop.symm h3b
  have hAbs : (3 * a * a - b * b).natAbs =
      (b * b - 3 * a * a).natAbs := by
    rw [← Int.natAbs_neg]
    congr 1
    ring
  rw [hAbs]
  exact h

/-! ## Witness-rich coordinate data -/

private theorem coordinate_oppositeParity
    {A B : ℕ} {a b : ℤ}
    (hAB : Nat.Coprime A B)
    (hcop : Nat.Coprime a.natAbs b.natAbs)
    (hRe : (A : ℤ) ^ 2 = a * (a * a - 3 * b * b))
    (hIm : (B : ℤ) ^ 2 = b * (3 * a * a - b * b)) :
    (Even a.natAbs ∧ ¬Even b.natAbs) ∨
      (¬Even a.natAbs ∧ Even b.natAbs) := by
  rcases Int.even_or_odd a with ha | ha <;>
    rcases Int.even_or_odd b with hb | hb
  · exfalso
    exact not_both_even_of_coprime hcop
      ⟨Int.natAbs_even.mpr ha, Int.natAbs_even.mpr hb⟩
  · exact Or.inl ⟨Int.natAbs_even.mpr ha,
      fun h ↦ Int.not_odd_iff_even.mpr (Int.natAbs_even.mp h) hb⟩
  · exact Or.inr ⟨(fun h ↦
      Int.not_odd_iff_even.mpr (Int.natAbs_even.mp h) ha),
      Int.natAbs_even.mpr hb⟩
  · exfalso
    have hfEven : Even (a * a - 3 * b * b) :=
      (ha.mul ha).sub_odd (((by norm_num : Odd (3 : ℤ)).mul hb).mul hb)
    have hgEven : Even (3 * a * a - b * b) :=
      (((by norm_num : Odd (3 : ℤ)).mul ha).mul ha).sub_odd (hb.mul hb)
    have hAIntEven : Even ((A : ℤ) ^ 2) := by
      rw [hRe]
      exact hfEven.mul_left a
    have hBIntEven : Even ((B : ℤ) ^ 2) := by
      rw [hIm]
      exact hgEven.mul_left b
    have hANatEven : Even (A ^ 2) := by exact_mod_cast hAIntEven
    have hBNatEven : Even (B ^ 2) := by exact_mod_cast hBIntEven
    have hAEven : Even A := by
      simpa only [Nat.even_pow' (by norm_num : (2 : ℕ) ≠ 0)] using hANatEven
    have hBEven : Even B := by
      simpa only [Nat.even_pow' (by norm_num : (2 : ℕ) ≠ 0)] using hBNatEven
    exact not_both_even_of_coprime hAB ⟨hAEven, hBEven⟩

structure GaussianCoordinateDescentData (A B : ℕ) where
  a : ℤ
  b : ℤ
  coordinate_coprime : Nat.Coprime a.natAbs b.natAbs
  coordinate_oppositeParity :
    (Even a.natAbs ∧ ¬Even b.natAbs) ∨
      (¬Even a.natAbs ∧ Even b.natAbs)
  real_coordinate_eq :
    (A : ℤ) ^ 2 = a * (a * a - 3 * b * b)
  imaginary_coordinate_eq :
    (B : ℤ) ^ 2 = b * (3 * a * a - b * b)
  real_coordinate_product_pos : 0 < a * (a * a - 3 * b * b)
  imaginary_coordinate_product_pos : 0 < b * (3 * a * a - b * b)
  real_square_split :
    RegularSquareSplit a.natAbs (a * a - 3 * b * b).natAbs A ∨
      ExceptionalThreeSquareSplit a.natAbs
        (a * a - 3 * b * b).natAbs A
  imaginary_square_split :
    RegularSquareSplit b.natAbs (3 * a * a - b * b).natAbs B ∨
      ExceptionalThreeSquareSplit b.natAbs
        (3 * a * a - b * b).natAbs B
  not_both_coordinates_divisible_by_three :
    ¬(3 ∣ a.natAbs ∧ 3 ∣ b.natAbs)

theorem exists_coordinate_descent_data
    {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Nat.Coprime A B) {a b : ℤ}
    (hcopInt : IsCoprime a b)
    (hRe : (A : ℤ) ^ 2 = a * (a ^ 2 - 3 * b ^ 2))
    (hIm : (B : ℤ) ^ 2 = b * (3 * a ^ 2 - b ^ 2)) :
    Nonempty (GaussianCoordinateDescentData A B) := by
  have hcop : Nat.Coprime a.natAbs b.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hcopInt
  have hRe' : (A : ℤ) ^ 2 = a * (a * a - 3 * b * b) := by
    calc
      (A : ℤ) ^ 2 = a * (a ^ 2 - 3 * b ^ 2) := hRe
      _ = a * (a * a - 3 * b * b) := by ring
  have hIm' : (B : ℤ) ^ 2 = b * (3 * a * a - b * b) := by
    calc
      (B : ℤ) ^ 2 = b * (3 * a ^ 2 - b ^ 2) := hIm
      _ = b * (3 * a * a - b * b) := by ring
  have hReNat : A ^ 2 = a.natAbs * (a * a - 3 * b * b).natAbs := by
    have h := congrArg Int.natAbs hRe'
    simpa only [Int.natAbs_pow, Int.natAbs_natCast, Int.natAbs_mul] using h
  have hImNat : B ^ 2 = b.natAbs * (3 * a * a - b * b).natAbs := by
    have h := congrArg Int.natAbs hIm'
    simpa only [Int.natAbs_pow, Int.natAbs_natCast, Int.natAbs_mul] using h
  have hReGcdDvd := re_factor_gcd_dvd_three hcop
  have hImGcdDvd := im_factor_gcd_dvd_three hcop
  have hReGcdIff := re_factor_gcd_eq_three_iff hcop
  have hImGcdIff := im_factor_gcd_eq_three_iff hcop
  have hReSplit := squareProductSplitAtThree hReGcdDvd
    (fun hg ↦ re_factor_not_nine_dvd hcop (hReGcdIff.mp hg)) hReNat.symm
  have hImSplit := squareProductSplitAtThree hImGcdDvd
    (fun hg ↦ im_factor_not_nine_dvd hcop (hImGcdIff.mp hg)) hImNat.symm
  have hNotBoth : ¬(3 ∣ a.natAbs ∧ 3 ∣ b.natAbs) := by
    rintro ⟨h3a, h3b⟩
    have h3cop : Nat.Coprime 3 b.natAbs :=
      Nat.Coprime.of_dvd_left h3a hcop
    exact (Nat.prime_three.coprime_iff_not_dvd.mp h3cop) h3b
  have hAPos : 0 < A ^ 2 := pow_pos (Nat.pos_of_ne_zero hA) 2
  have hBPos : 0 < B ^ 2 := pow_pos (Nat.pos_of_ne_zero hB) 2
  have hRePos : 0 < a * (a * a - 3 * b * b) := by
    rw [← hRe']
    exact_mod_cast hAPos
  have hImPos : 0 < b * (3 * a * a - b * b) := by
    rw [← hIm']
    exact_mod_cast hBPos
  exact ⟨{
    a := a
    b := b
    coordinate_coprime := hcop
    coordinate_oppositeParity := coordinate_oppositeParity hAB hcop hRe' hIm'
    real_coordinate_eq := hRe'
    imaginary_coordinate_eq := hIm'
    real_coordinate_product_pos := hRePos
    imaginary_coordinate_product_pos := hImPos
    real_square_split := hReSplit
    imaginary_square_split := hImSplit
    not_both_coordinates_divisible_by_three := hNotBoth
  }⟩

theorem GaussianCoordinateDescentData.not_both_square_splits_exceptional
    {A B : ℕ} (d : GaussianCoordinateDescentData A B) :
    ¬(ExceptionalThreeSquareSplit d.a.natAbs
        (d.a * d.a - 3 * d.b * d.b).natAbs A ∧
      ExceptionalThreeSquareSplit d.b.natAbs
        (3 * d.a * d.a - d.b * d.b).natAbs B) := by
  rintro ⟨hReal, hImag⟩
  rcases hReal with ⟨r, s, hRealCoordinate, -, -, -, -⟩
  rcases hImag with ⟨u, v, hImagCoordinate, -, -, -, -⟩
  apply d.not_both_coordinates_divisible_by_three
  constructor
  · rw [hRealCoordinate]
    exact dvd_mul_right 3 (r ^ 2)
  · rw [hImagCoordinate]
    exact dvd_mul_right 3 (u ^ 2)

/-! ## Modulo-eight exclusion of the regular/regular branch -/

private theorem odd_square_mod_eight {n : ℕ} (hn : ¬Even n) :
    n ^ 2 % 8 = 1 := by
  have hFinite : ∀ m : Fin 8, m.val % 2 = 1 → m.val ^ 2 % 8 = 1 := by
    decide
  have hModOdd : (n % 8) % 2 = 1 :=
    (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).trans
      (Nat.not_even_iff.mp hn)
  calc
    n ^ 2 % 8 = (n % 8) ^ 2 % 8 := by rw [Nat.pow_mod]
    _ = 1 := hFinite ⟨n % 8, Nat.mod_lt n (by norm_num)⟩ hModOdd

private theorem natAbs_not_square_of_zmod_eight_eq_three_or_five {x : ℤ}
    (hx : (x : ZMod 8) = 3 ∨ (x : ZMod 8) = 5) :
    ¬∃ s : ℕ, x.natAbs = s ^ 2 := by
  rintro ⟨s, hs⟩
  have hFinite : ∀ y : ZMod 8, y ^ 2 ≠ 3 ∧ y ^ 2 ≠ 5 := by decide
  have hSquare : ((((x.natAbs : ℕ) : ℤ) : ZMod 8)) =
      (s : ZMod 8) ^ 2 := by
    rw [hs]
    norm_num
  rcases Int.natAbs_eq x with hSign | hSign
  · have hCast := congrArg (fun z : ℤ ↦ (z : ZMod 8)) hSign
    change (x : ZMod 8) = ((((x.natAbs : ℕ) : ℤ) : ZMod 8)) at hCast
    rcases hx with hx | hx
    · apply (hFinite (s : ZMod 8)).1
      rw [← hSquare]
      exact hCast.symm.trans hx
    · apply (hFinite (s : ZMod 8)).2
      rw [← hSquare]
      exact hCast.symm.trans hx
  · have hCast := congrArg (fun z : ℤ ↦ (z : ZMod 8)) hSign
    norm_num only [Int.cast_neg] at hCast
    have hNat : ((((x.natAbs : ℕ) : ℤ) : ZMod 8)) =
        -(x : ZMod 8) := by
      rw [hCast]
      ring
    rcases hx with hx | hx
    · apply (hFinite (s : ZMod 8)).2
      rw [← hSquare, hNat, hx]
      decide
    · apply (hFinite (s : ZMod 8)).1
      rw [← hSquare, hNat, hx]
      decide

private theorem int_mul_self_eq_natAbs_mul_self (a : ℤ) :
    a * a = ((a.natAbs * a.natAbs : ℕ) : ℤ) := by
  simpa only [Int.natCast_mul, Int.natCast_natAbs] using
    (abs_mul_abs_self a).symm

private theorem even_fourth_power_mod_sixteen {n : ℕ} (hn : Even n) :
    n ^ 4 % 16 = 0 := by
  rcases hn with ⟨k, rfl⟩
  apply Nat.dvd_iff_mod_eq_zero.mp
  refine ⟨k ^ 4, ?_⟩
  ring

private theorem no_regular_re_square_split_of_even_re_odd_im
    {a b : ℤ} {A : ℕ}
    (hParity : Even a.natAbs ∧ ¬Even b.natAbs)
    (hRegular : RegularSquareSplit a.natAbs
      (a * a - 3 * b * b).natAbs A) : False := by
  rcases hRegular with ⟨r, s, haAbs, hfAbs, -, -⟩
  have hrEven : Even r := by
    apply ((Nat.even_pow (m := r) (n := 2)).mp ?_).1
    simpa only [← haAbs] using hParity.1
  have hrFourth16 : r ^ 4 % 16 = 0 :=
    even_fourth_power_mod_sixteen hrEven
  have hrFourth8 : r ^ 4 % 8 = 0 := by
    rw [← Nat.mod_mod_of_dvd (r ^ 4) (by decide : 8 ∣ 16), hrFourth16]
  have haSq : a * a = ((a.natAbs * a.natAbs : ℕ) : ℤ) :=
    int_mul_self_eq_natAbs_mul_self a
  have hbSq : b * b = ((b.natAbs * b.natAbs : ℕ) : ℤ) :=
    int_mul_self_eq_natAbs_mul_self b
  have haZ : ((a * a : ℤ) : ZMod 8) = 0 := by
    rw [haSq, haAbs]
    norm_num only [Int.cast_natCast]
    rw [show r ^ 2 * r ^ 2 = r ^ 4 by ring]
    rw [← ZMod.natCast_mod (r ^ 4) 8, hrFourth8]
    norm_num
  have hbMod : b.natAbs ^ 2 % 8 = 1 := odd_square_mod_eight hParity.2
  have hbZ : ((b * b : ℤ) : ZMod 8) = 1 := by
    rw [hbSq]
    norm_num only [Int.cast_natCast]
    rw [show b.natAbs * b.natAbs = b.natAbs ^ 2 by ring]
    rw [← ZMod.natCast_mod (b.natAbs ^ 2) 8, hbMod]
    norm_num
  apply natAbs_not_square_of_zmod_eight_eq_three_or_five
    (x := a * a - 3 * b * b) (Or.inr ?_) ⟨s, hfAbs⟩
  push_cast
  norm_num only [Int.cast_mul] at haZ hbZ
  rw [haZ, mul_assoc, hbZ]
  decide

private theorem no_regular_im_square_split_of_even_im_odd_re
    {a b : ℤ} {B : ℕ}
    (hParity : Even b.natAbs ∧ ¬Even a.natAbs)
    (hRegular : RegularSquareSplit b.natAbs
      (3 * a * a - b * b).natAbs B) : False := by
  have hAbs : (b * b - 3 * a * a).natAbs =
      (3 * a * a - b * b).natAbs := by
    rw [← Int.natAbs_neg]
    congr 1
    ring
  have hRegular' : RegularSquareSplit b.natAbs
      (b * b - 3 * a * a).natAbs B := by
    simpa only [hAbs] using hRegular
  exact no_regular_re_square_split_of_even_re_odd_im
    (a := b) (b := a) ⟨hParity.1, hParity.2⟩ hRegular'

theorem GaussianCoordinateDescentData.not_both_square_splits_regular
    {A B : ℕ} (d : GaussianCoordinateDescentData A B) :
    ¬(RegularSquareSplit d.a.natAbs
        (d.a * d.a - 3 * d.b * d.b).natAbs A ∧
      RegularSquareSplit d.b.natAbs
        (3 * d.a * d.a - d.b * d.b).natAbs B) := by
  rintro ⟨hReal, hImaginary⟩
  rcases d.coordinate_oppositeParity with hParity | hParity
  · exact no_regular_re_square_split_of_even_re_odd_im hParity hReal
  · exact no_regular_im_square_split_of_even_im_odd_re
      ⟨hParity.2, hParity.1⟩ hImaginary

def GaussianCoordinateMixedSquareSplits {A B : ℕ}
    (d : GaussianCoordinateDescentData A B) : Prop :=
  (RegularSquareSplit d.a.natAbs
      (d.a * d.a - 3 * d.b * d.b).natAbs A ∧
    ExceptionalThreeSquareSplit d.b.natAbs
      (3 * d.a * d.a - d.b * d.b).natAbs B) ∨
  (ExceptionalThreeSquareSplit d.a.natAbs
      (d.a * d.a - 3 * d.b * d.b).natAbs A ∧
    RegularSquareSplit d.b.natAbs
      (3 * d.a * d.a - d.b * d.b).natAbs B)

theorem GaussianCoordinateDescentData.mixed_square_splits
    {A B : ℕ} (d : GaussianCoordinateDescentData A B) :
    GaussianCoordinateMixedSquareSplits d := by
  rcases d.real_square_split with hReal | hReal <;>
    rcases d.imaginary_square_split with hImaginary | hImaginary
  · exact (d.not_both_square_splits_regular ⟨hReal, hImaginary⟩).elim
  · exact Or.inl ⟨hReal, hImaginary⟩
  · exact Or.inr ⟨hReal, hImaginary⟩
  · exact (d.not_both_square_splits_exceptional
      ⟨hReal, hImaginary⟩).elim

/-! ## Extraction of the auxiliary quartic-three equation -/

private theorem zmod_three_no_wrong_quartic_orientation :
    ∀ x q : ZMod 3, x ≠ 0 → 0 ≠ x ^ 4 + q ^ 2 := by
  decide

private theorem no_three_mul_fourth_eq_fourth_add_square
    {x y q : ℕ} (h3x : ¬3 ∣ x)
    (hEq : 3 * y ^ 4 = x ^ 4 + q ^ 2) : False := by
  have hxZ : (x : ZMod 3) ≠ 0 := by
    intro hx
    exact h3x ((ZMod.natCast_eq_zero_iff x 3).mp hx)
  have hEqZ := congrArg (fun n : ℕ ↦ (n : ZMod 3)) hEq
  have hZero : (0 : ZMod 3) = (x : ZMod 3) ^ 4 + (q : ZMod 3) ^ 2 := by
    norm_num only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add,
      Nat.cast_pow] at hEqZ
    rw [show (3 : ZMod 3) = 0 by exact ZMod.natCast_self 3,
      zero_mul] at hEqZ
    exact hEqZ
  exact zmod_three_no_wrong_quartic_orientation (x : ZMod 3)
    (q : ZMod 3) hxZ hZero

private theorem square_root_coprime_of_scaled_square_coordinates
    {r u : ℕ} (h : Nat.Coprime (r ^ 2) (3 * u ^ 2)) :
    Nat.Coprime r u := by
  have hSquares : Nat.Coprime (r ^ 2) (u ^ 2) :=
    Nat.Coprime.of_dvd_right (by exact dvd_mul_left (u ^ 2) 3) h
  have hLeft : Nat.Coprime r (u ^ 2) :=
    (Nat.coprime_pow_left_iff (by norm_num) r (u ^ 2)).mp hSquares
  exact (Nat.coprime_pow_right_iff (by norm_num) r u).mp hLeft

private theorem three_not_dvd_regular_root_of_scaled_square_coordinates
    {r u : ℕ} (h : Nat.Coprime (r ^ 2) (3 * u ^ 2)) : ¬3 ∣ r := by
  intro h3r
  have h3rSq : 3 ∣ r ^ 2 := dvd_pow h3r (by norm_num : (2 : ℕ) ≠ 0)
  have hCoprime3 : Nat.Coprime 3 (3 * u ^ 2) :=
    Nat.Coprime.of_dvd_left h3rSq h
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hCoprime3)
    (dvd_mul_right 3 (u ^ 2))

private theorem root_ne_zero_of_natAbs_eq_square
    {a : ℤ} {r : ℕ} (ha : a ≠ 0) (h : a.natAbs = r ^ 2) : r ≠ 0 := by
  intro hr
  apply ha
  apply Int.natAbs_eq_zero.mp
  rw [h, hr]
  norm_num

private theorem root_ne_zero_of_natAbs_eq_three_mul_square
    {a : ℤ} {r : ℕ} (ha : a ≠ 0)
    (h : a.natAbs = 3 * r ^ 2) : r ≠ 0 := by
  intro hr
  apply ha
  apply Int.natAbs_eq_zero.mp
  rw [h, hr]
  norm_num

private theorem false_of_regular_re_exceptional_im
    {A B : ℕ} (d : GaussianCoordinateDescentData A B)
    (hReal : RegularSquareSplit d.a.natAbs
      (d.a * d.a - 3 * d.b * d.b).natAbs A)
    (hImaginary : ExceptionalThreeSquareSplit d.b.natAbs
      (3 * d.a * d.a - d.b * d.b).natAbs B) : False := by
  rcases hReal with ⟨r, s, ha, hf, -, -⟩
  rcases hImaginary with ⟨u, v, hb, hg, -, -, -⟩
  have hCoordinateCoprime : Nat.Coprime (r ^ 2) (3 * u ^ 2) := by
    simpa only [ha, hb] using d.coordinate_coprime
  have hru : Nat.Coprime r u :=
    square_root_coprime_of_scaled_square_coordinates hCoordinateCoprime
  have h3r : ¬3 ∣ r :=
    three_not_dvd_regular_root_of_scaled_square_coordinates hCoordinateCoprime
  have haSq : d.a * d.a = (r : ℤ) ^ 4 := by
    calc
      d.a * d.a = ((d.a.natAbs * d.a.natAbs : ℕ) : ℤ) :=
        int_mul_self_eq_natAbs_mul_self d.a
      _ = (((r ^ 2) * (r ^ 2) : ℕ) : ℤ) := by rw [ha]
      _ = (r : ℤ) ^ 4 := by norm_num; ring
  have hbSq : d.b * d.b = 9 * (u : ℤ) ^ 4 := by
    calc
      d.b * d.b = ((d.b.natAbs * d.b.natAbs : ℕ) : ℤ) :=
        int_mul_self_eq_natAbs_mul_self d.b
      _ = (((3 * u ^ 2) * (3 * u ^ 2) : ℕ) : ℤ) := by rw [hb]
      _ = 9 * (u : ℤ) ^ 4 := by norm_num; ring
  let g := 3 * d.a * d.a - d.b * d.b
  have hgAbs : g.natAbs = 3 * v ^ 2 := by simpa only [g] using hg
  have hEquation : r ^ 4 = 3 * u ^ 4 + v ^ 2 := by
    rcases Int.natAbs_eq g with hSign | hSign
    · have hSign' : g = ((3 * v ^ 2 : ℕ) : ℤ) := by
        rw [hSign, hgAbs]
      have hInt : (r : ℤ) ^ 4 =
          3 * (u : ℤ) ^ 4 + (v : ℤ) ^ 2 := by
        dsimp only [g] at hSign'
        norm_num at hSign' ⊢
        nlinarith [haSq, hbSq]
      exact_mod_cast hInt
    · have hSign' : g = -((3 * v ^ 2 : ℕ) : ℤ) := by
        rw [hSign, hgAbs]
      have hWrongInt : (3 : ℤ) * (u : ℤ) ^ 4 =
          (r : ℤ) ^ 4 + (v : ℤ) ^ 2 := by
        dsimp only [g] at hSign'
        norm_num at hSign' ⊢
        nlinarith [haSq, hbSq]
      have hWrong : 3 * u ^ 4 = r ^ 4 + v ^ 2 := by exact_mod_cast hWrongInt
      exact (no_three_mul_fourth_eq_fourth_add_square h3r hWrong).elim
  have haNe : d.a ≠ 0 :=
    left_ne_zero_of_mul (ne_of_gt d.real_coordinate_product_pos)
  have hbNe : d.b ≠ 0 :=
    left_ne_zero_of_mul (ne_of_gt d.imaginary_coordinate_product_pos)
  have hrNe := root_ne_zero_of_natAbs_eq_square haNe ha
  have huNe := root_ne_zero_of_natAbs_eq_three_mul_square hbNe hb
  exact no_primitive_quartic_three hrNe huNe hru hEquation

private theorem false_of_exceptional_re_regular_im
    {A B : ℕ} (d : GaussianCoordinateDescentData A B)
    (hReal : ExceptionalThreeSquareSplit d.a.natAbs
      (d.a * d.a - 3 * d.b * d.b).natAbs A)
    (hImaginary : RegularSquareSplit d.b.natAbs
      (3 * d.a * d.a - d.b * d.b).natAbs B) : False := by
  rcases hReal with ⟨r, s, ha, hf, -, -, -⟩
  rcases hImaginary with ⟨u, v, hb, hg, -, -⟩
  have hCoordinateCoprime : Nat.Coprime (u ^ 2) (3 * r ^ 2) := by
    have h := d.coordinate_coprime.symm
    simpa only [ha, hb] using h
  have hur : Nat.Coprime u r :=
    square_root_coprime_of_scaled_square_coordinates hCoordinateCoprime
  have h3u : ¬3 ∣ u :=
    three_not_dvd_regular_root_of_scaled_square_coordinates hCoordinateCoprime
  have haSq : d.a * d.a = 9 * (r : ℤ) ^ 4 := by
    calc
      d.a * d.a = ((d.a.natAbs * d.a.natAbs : ℕ) : ℤ) :=
        int_mul_self_eq_natAbs_mul_self d.a
      _ = (((3 * r ^ 2) * (3 * r ^ 2) : ℕ) : ℤ) := by rw [ha]
      _ = 9 * (r : ℤ) ^ 4 := by norm_num; ring
  have hbSq : d.b * d.b = (u : ℤ) ^ 4 := by
    calc
      d.b * d.b = ((d.b.natAbs * d.b.natAbs : ℕ) : ℤ) :=
        int_mul_self_eq_natAbs_mul_self d.b
      _ = (((u ^ 2) * (u ^ 2) : ℕ) : ℤ) := by rw [hb]
      _ = (u : ℤ) ^ 4 := by norm_num; ring
  let f := d.a * d.a - 3 * d.b * d.b
  have hfAbs : f.natAbs = 3 * s ^ 2 := by simpa only [f] using hf
  have hEquation : u ^ 4 = 3 * r ^ 4 + s ^ 2 := by
    rcases Int.natAbs_eq f with hSign | hSign
    · have hSign' : f = ((3 * s ^ 2 : ℕ) : ℤ) := by
        rw [hSign, hfAbs]
      have hWrongInt : (3 : ℤ) * (r : ℤ) ^ 4 =
          (u : ℤ) ^ 4 + (s : ℤ) ^ 2 := by
        dsimp only [f] at hSign'
        norm_num at hSign' ⊢
        nlinarith [haSq, hbSq]
      have hWrong : 3 * r ^ 4 = u ^ 4 + s ^ 2 := by exact_mod_cast hWrongInt
      exact (no_three_mul_fourth_eq_fourth_add_square h3u hWrong).elim
    · have hSign' : f = -((3 * s ^ 2 : ℕ) : ℤ) := by
        rw [hSign, hfAbs]
      have hInt : (u : ℤ) ^ 4 =
          3 * (r : ℤ) ^ 4 + (s : ℤ) ^ 2 := by
        dsimp only [f] at hSign'
        norm_num at hSign' ⊢
        nlinarith [haSq, hbSq]
      exact_mod_cast hInt
  have haNe : d.a ≠ 0 :=
    left_ne_zero_of_mul (ne_of_gt d.real_coordinate_product_pos)
  have hbNe : d.b ≠ 0 :=
    left_ne_zero_of_mul (ne_of_gt d.imaginary_coordinate_product_pos)
  have huNe := root_ne_zero_of_natAbs_eq_square hbNe hb
  have hrNe := root_ne_zero_of_natAbs_eq_three_mul_square haNe ha
  exact no_primitive_quartic_three huNe hrNe hur hEquation

/-- The full bridge: a primitive nonzero `(4,4,3)` equation is impossible. -/
theorem no_primitive_four_four_three
    {A B C : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Nat.Coprime A B) (hEq : A ^ 4 + B ^ 4 = C ^ 3) : False := by
  have hOdd := fourth_sum_odd_of_coprime_eq_cube hAB hEq
  obtain ⟨a, b, hcop, hRe, hIm⟩ :=
    primitive_sum_square_cube_parametrization hAB hOdd hEq
  obtain ⟨d⟩ := exists_coordinate_descent_data hA hB hAB hcop hRe hIm
  rcases d.mixed_square_splits with h | h
  · exact false_of_regular_re_exceptional_im d h.1 h.2
  · exact false_of_exceptional_re_regular_im d h.1 h.2

/-- Convenience wrapper for callers already carrying pairwise coprimality. -/
theorem no_pairwise_coprime_nonzero_four_four_three
    {A B C : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (_hC : C ≠ 0)
    (hAB : Nat.Coprime A B) (_hAC : Nat.Coprime A C)
    (_hBC : Nat.Coprime B C) (hEq : A ^ 4 + B ^ 4 = C ^ 3) : False := by
  exact no_primitive_four_four_three hA hB hAB hEq

/-- Exact Beal boundary for the solved normalized signature `(4,4,3)`: every
nonzero natural solution has one prime dividing all three bases. -/
theorem four_four_three_hasCommonPrimeFactor
    {A B C : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (_hC : C ≠ 0)
    (hEq : A ^ 4 + B ^ 4 = C ^ 3) : HasCommonPrimeFactor A B C := by
  by_cases hAB : Nat.Coprime A B
  · exact (no_primitive_four_four_three hA hB hAB hEq).elim
  · have hgcd : Nat.gcd A B ≠ 1 := by
      intro hgcd
      exact hAB (Nat.coprime_iff_gcd_eq_one.mpr hgcd)
    obtain ⟨p, hp, hpGcd⟩ := Nat.exists_prime_and_dvd hgcd
    have hpA : p ∣ A := hpGcd.trans (Nat.gcd_dvd_left A B)
    have hpB : p ∣ B := hpGcd.trans (Nat.gcd_dvd_right A B)
    have hpCcube : p ∣ C ^ 3 := by
      rw [← hEq]
      exact dvd_add (dvd_pow hpA (by norm_num)) (dvd_pow hpB (by norm_num))
    exact ⟨p, hp, hpA, hpB, hp.dvd_of_dvd_pow hpCcube⟩

end BealRegular.GaussianQuarticThreeBridge
