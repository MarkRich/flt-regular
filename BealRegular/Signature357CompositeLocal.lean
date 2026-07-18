import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

/-!
# Three-adic composite-modulus restrictions for `(3,5,7)`

This file records three branch-sensitive restrictions for a pairwise-coprime
natural identity, possibly with a zero base,

`A ^ 3 + B ^ 5 = C ^ 7`.

They use the composite moduli `27 = 3^3` and `243 = 3^5`.  When one base is
divisible by three, pairwise coprimality makes the other two bases units.  The
powered divisible term then vanishes, and a finite unit calculation gives:

* `3 ∣ B  ->  C = ±1    (mod 9)`;
* `3 ∣ C  ->  B = ±1    (mod 9)`;
* `3 ∣ A  ->  B = C^5   (mod 27)`;
* `3 ∣ B  ->  C = A^93  (mod 243)`;
* `3 ∣ C  ->  B = -A^33 (mod 243)`.

These are conditional implications, not an exhaustive branch split: the file
does not prove that any base is divisible by three, exclude any branch, or
prove nonexistence for the `(3,5,7)` signature.

The modulo-27 unit calculations use ordinary kernel `decide`.  At modulus 243
the proof uses Euler's theorem for the unit group and checks the exponent
arithmetic symbolically, avoiding a large pairwise truth table.  The public
theorem proves the transport from pairwise-coprime natural numbers; the
discovery scan is not part of Lean's trusted proof.
-/

namespace BealRegular.Signature357CompositeLocal

/-! ## Kernel-checked unit calculations -/

private theorem mod9_cubic_eq_seventh_units :
    ∀ a c : ZMod 9,
      IsUnit a → IsUnit c → a ^ 3 = c ^ 7 → c = 1 ∨ c = 8 := by
  decide

private theorem mod9_cubic_plus_fifth_units :
    ∀ a b : ZMod 9,
      IsUnit a → IsUnit b → a ^ 3 + b ^ 5 = 0 → b = 1 ∨ b = 8 := by
  decide

private theorem mod27_fifth_inverse_units :
    ∀ b : ZMod 27, IsUnit b → (b ^ 5) ^ 11 = b := by
  decide

private theorem mod27_seventh_then_eleventh_units :
    ∀ c : ZMod 27, IsUnit c → (c ^ 7) ^ 11 = c ^ 5 := by
  decide

private theorem mod243_unit_pow_162 {a : ZMod 243} (ha : IsUnit a) :
    a ^ 162 = 1 := by
  let u : (ZMod 243)ˣ := ha.unit
  have hu : u ^ Nat.totient 243 = 1 := ZMod.pow_totient u
  have hv := congrArg (fun x : (ZMod 243)ˣ => (x : ZMod 243)) hu
  have htot : Nat.totient 243 = 162 := by
    rw [show 243 = 3 ^ 5 by norm_num]
    rw [Nat.totient_prime_pow Nat.prime_three (by norm_num : 0 < 5)]
    norm_num
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, htot, u,
    IsUnit.unit_spec] using hv

private theorem mod243_seventh_inverse_units
    {c : ZMod 243} (hc : IsUnit c) :
    (c ^ 7) ^ 139 = c := by
  have hEuler := mod243_unit_pow_162 hc
  calc
    (c ^ 7) ^ 139 = c ^ (7 * 139) := (pow_mul c 7 139).symm
    _ = c ^ (162 * 6 + 1) := by norm_num
    _ = (c ^ 162) ^ 6 * c := by rw [pow_add, pow_mul, pow_one]
    _ = c := by rw [hEuler]; simp

private theorem mod243_cubic_then_139_units
    {a : ZMod 243} (ha : IsUnit a) :
    (a ^ 3) ^ 139 = a ^ 93 := by
  have hEuler := mod243_unit_pow_162 ha
  calc
    (a ^ 3) ^ 139 = a ^ (3 * 139) := (pow_mul a 3 139).symm
    _ = a ^ (162 * 2 + 93) := by norm_num
    _ = (a ^ 162) ^ 2 * a ^ 93 := by rw [pow_add, pow_mul]
    _ = a ^ 93 := by rw [hEuler]; simp

private theorem mod243_fifth_inverse_units
    {b : ZMod 243} (hb : IsUnit b) :
    (b ^ 5) ^ 65 = b := by
  have hEuler := mod243_unit_pow_162 hb
  calc
    (b ^ 5) ^ 65 = b ^ (5 * 65) := (pow_mul b 5 65).symm
    _ = b ^ (162 * 2 + 1) := by norm_num
    _ = (b ^ 162) ^ 2 * b := by rw [pow_add, pow_mul, pow_one]
    _ = b := by rw [hEuler]; simp

private theorem mod243_neg_cubic_then_65_units
    {a : ZMod 243} (ha : IsUnit a) :
    (-(a ^ 3)) ^ 65 + a ^ 33 = 0 := by
  have hEuler := mod243_unit_pow_162 ha
  calc
    (-(a ^ 3)) ^ 65 + a ^ 33 = -(a ^ 3) ^ 65 + a ^ 33 := by
      rw [(by decide : Odd 65).neg_pow]
    _ = -(a ^ (3 * 65)) + a ^ 33 := by rw [pow_mul]
    _ = -(a ^ (162 + 33)) + a ^ 33 := by norm_num
    _ = -((a ^ 162) * a ^ 33) + a ^ 33 := by rw [pow_add]
    _ = 0 := by rw [hEuler]; ring

private theorem mod27_fifth_eq_seventh_units
    {b c : ZMod 27} (hb : IsUnit b) (hc : IsUnit c)
    (hEq : b ^ 5 = c ^ 7) :
    b = c ^ 5 := by
  calc
    b = (b ^ 5) ^ 11 := (mod27_fifth_inverse_units b hb).symm
    _ = (c ^ 7) ^ 11 := congrArg (fun x : ZMod 27 => x ^ 11) hEq
    _ = c ^ 5 := mod27_seventh_then_eleventh_units c hc

private theorem mod243_cubic_eq_seventh_units
    {a c : ZMod 243} (ha : IsUnit a) (hc : IsUnit c)
    (hEq : a ^ 3 = c ^ 7) :
    c = a ^ 93 := by
  calc
    c = (c ^ 7) ^ 139 := (mod243_seventh_inverse_units hc).symm
    _ = (a ^ 3) ^ 139 :=
      congrArg (fun x : ZMod 243 => x ^ 139) hEq.symm
    _ = a ^ 93 := mod243_cubic_then_139_units ha

private theorem mod243_cubic_plus_fifth_units
    {a b : ZMod 243} (ha : IsUnit a) (hb : IsUnit b)
    (hEq : a ^ 3 + b ^ 5 = 0) :
    b + a ^ 33 = 0 := by
  have hPow : b ^ 5 = -(a ^ 3) := eq_neg_of_add_eq_zero_right hEq
  calc
    b + a ^ 33 = (b ^ 5) ^ 65 + a ^ 33 := by
      rw [mod243_fifth_inverse_units hb]
    _ = (-(a ^ 3)) ^ 65 + a ^ 33 := by rw [hPow]
    _ = 0 := mod243_neg_cubic_then_65_units ha

/-! ## Transport helpers -/

private theorem not_three_dvd_right_of_coprime_of_dvd_left
    {x y : ℕ} (hxy : Nat.Coprime x y) (hx : 3 ∣ x) : ¬3 ∣ y := by
  have h3y : Nat.Coprime 3 y := Nat.Coprime.of_dvd_left hx hxy
  exact Nat.prime_three.coprime_iff_not_dvd.mp h3y

private theorem isUnit_zmod27_of_not_three_dvd {n : ℕ} (hn : ¬3 ∣ n) :
    IsUnit (n : ZMod 27) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 27 = 3 ^ 3 by norm_num] using
    Nat.prime_three.coprime_pow_of_not_dvd hn (m := 3)

private theorem isUnit_zmod9_of_not_three_dvd {n : ℕ} (hn : ¬3 ∣ n) :
    IsUnit (n : ZMod 9) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 9 = 3 ^ 2 by norm_num] using
    Nat.prime_three.coprime_pow_of_not_dvd hn (m := 2)

private theorem isUnit_zmod243_of_not_three_dvd {n : ℕ} (hn : ¬3 ∣ n) :
    IsUnit (n : ZMod 243) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 243 = 3 ^ 5 by norm_num] using
    Nat.prime_three.coprime_pow_of_not_dvd hn (m := 5)

private theorem cube_cast_eq_zero_mod27_of_three_dvd {n : ℕ}
    (hn : 3 ∣ n) :
    (n : ZMod 27) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  use k ^ 3
  ring

private theorem fifth_cast_eq_zero_mod243_of_three_dvd {n : ℕ}
    (hn : 3 ∣ n) :
    (n : ZMod 243) ^ 5 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  use k ^ 5
  ring

private theorem fifth_cast_eq_zero_mod9_of_three_dvd {n : ℕ}
    (hn : 3 ∣ n) :
    (n : ZMod 9) ^ 5 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  use 27 * k ^ 5
  ring

private theorem seventh_cast_eq_zero_mod243_of_three_dvd {n : ℕ}
    (hn : 3 ∣ n) :
    (n : ZMod 243) ^ 7 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  use 9 * k ^ 7
  ring

private theorem seventh_cast_eq_zero_mod9_of_three_dvd {n : ℕ}
    (hn : 3 ∣ n) :
    (n : ZMod 9) ^ 7 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  use 243 * k ^ 7
  ring

/-! ## Natural-number restrictions -/

/-- The three branch-sensitive three-adic restrictions for a pairwise-coprime
solution of the `(3,5,7)` equation. -/
theorem signature357_three_adic_branch_table {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (hBC : Nat.Coprime B C)
    (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    (3 ∣ A → B % 27 = C ^ 5 % 27) ∧
    (3 ∣ B → C % 243 = A ^ 93 % 243) ∧
    (3 ∣ C → (B + A ^ 33) % 243 = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h3A
    have h3B : ¬3 ∣ B :=
      not_three_dvd_right_of_coprime_of_dvd_left hAB h3A
    have h3C : ¬3 ∣ C :=
      not_three_dvd_right_of_coprime_of_dvd_left hAC h3A
    have hEqZ :
        (A : ZMod 27) ^ 3 + (B : ZMod 27) ^ 5 =
          (C : ZMod 27) ^ 7 := by
      simpa only [Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ => (n : ZMod 27)) hEq
    have hBCZ : (B : ZMod 27) ^ 5 = (C : ZMod 27) ^ 7 := by
      rw [cube_cast_eq_zero_mod27_of_three_dvd h3A, zero_add] at hEqZ
      exact hEqZ
    have hZ : (B : ZMod 27) = (C : ZMod 27) ^ 5 :=
      mod27_fifth_eq_seventh_units
        (isUnit_zmod27_of_not_three_dvd h3B)
        (isUnit_zmod27_of_not_three_dvd h3C) hBCZ
    have hZ' : (B : ZMod 27) = (C ^ 5 : ℕ) := by
      simpa only [Nat.cast_pow] using hZ
    exact (ZMod.natCast_eq_natCast_iff' B (C ^ 5) 27).mp hZ'
  · intro h3B
    have h3A : ¬3 ∣ A :=
      not_three_dvd_right_of_coprime_of_dvd_left hAB.symm h3B
    have h3C : ¬3 ∣ C :=
      not_three_dvd_right_of_coprime_of_dvd_left hBC h3B
    have hEqZ :
        (A : ZMod 243) ^ 3 + (B : ZMod 243) ^ 5 =
          (C : ZMod 243) ^ 7 := by
      simpa only [Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ => (n : ZMod 243)) hEq
    have hACZ : (A : ZMod 243) ^ 3 = (C : ZMod 243) ^ 7 := by
      rw [fifth_cast_eq_zero_mod243_of_three_dvd h3B, add_zero] at hEqZ
      exact hEqZ
    have hZ : (C : ZMod 243) = (A : ZMod 243) ^ 93 :=
      mod243_cubic_eq_seventh_units
        (isUnit_zmod243_of_not_three_dvd h3A)
        (isUnit_zmod243_of_not_three_dvd h3C) hACZ
    have hZ' : (C : ZMod 243) = (A ^ 93 : ℕ) := by
      simpa only [Nat.cast_pow] using hZ
    exact (ZMod.natCast_eq_natCast_iff' C (A ^ 93) 243).mp hZ'
  · intro h3C
    have h3A : ¬3 ∣ A :=
      not_three_dvd_right_of_coprime_of_dvd_left hAC.symm h3C
    have h3B : ¬3 ∣ B :=
      not_three_dvd_right_of_coprime_of_dvd_left hBC.symm h3C
    have hEqZ :
        (A : ZMod 243) ^ 3 + (B : ZMod 243) ^ 5 =
          (C : ZMod 243) ^ 7 := by
      simpa only [Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ => (n : ZMod 243)) hEq
    have hABZ : (A : ZMod 243) ^ 3 + (B : ZMod 243) ^ 5 = 0 := by
      rw [seventh_cast_eq_zero_mod243_of_three_dvd h3C] at hEqZ
      exact hEqZ
    have hZ : (B : ZMod 243) + (A : ZMod 243) ^ 33 = 0 :=
      mod243_cubic_plus_fifth_units
        (isUnit_zmod243_of_not_three_dvd h3A)
        (isUnit_zmod243_of_not_three_dvd h3B) hABZ
    have hZ' : (B + A ^ 33 : ℕ) = (0 : ZMod 243) := by
      simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_zero] using hZ
    exact Nat.dvd_iff_mod_eq_zero.mp
      ((ZMod.natCast_eq_zero_iff (B + A ^ 33) 243).mp hZ')

/-- The genuinely new single-coordinate part of the composite scan.  If the
fifth- or seventh-power base is divisible by three, the indicated other base
is congruent to `±1` modulo nine. -/
theorem signature357_mod9_three_divisibility_coordinate_table {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (hBC : Nat.Coprime B C)
    (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    (3 ∣ B → C % 9 = 1 ∨ C % 9 = 8) ∧
    (3 ∣ C → B % 9 = 1 ∨ B % 9 = 8) := by
  constructor
  · intro h3B
    have h3A : ¬3 ∣ A :=
      not_three_dvd_right_of_coprime_of_dvd_left hAB.symm h3B
    have h3C : ¬3 ∣ C :=
      not_three_dvd_right_of_coprime_of_dvd_left hBC h3B
    have hEqZ :
        (A : ZMod 9) ^ 3 + (B : ZMod 9) ^ 5 = (C : ZMod 9) ^ 7 := by
      simpa only [Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ => (n : ZMod 9)) hEq
    have hACZ : (A : ZMod 9) ^ 3 = (C : ZMod 9) ^ 7 := by
      rw [fifth_cast_eq_zero_mod9_of_three_dvd h3B, add_zero] at hEqZ
      exact hEqZ
    rcases mod9_cubic_eq_seventh_units _ _
      (isUnit_zmod9_of_not_three_dvd h3A)
      (isUnit_zmod9_of_not_three_dvd h3C) hACZ with hC | hC
    · left
      exact (ZMod.natCast_eq_natCast_iff' C 1 9).mp (by simpa using hC)
    · right
      exact (ZMod.natCast_eq_natCast_iff' C 8 9).mp (by simpa using hC)
  · intro h3C
    have h3A : ¬3 ∣ A :=
      not_three_dvd_right_of_coprime_of_dvd_left hAC.symm h3C
    have h3B : ¬3 ∣ B :=
      not_three_dvd_right_of_coprime_of_dvd_left hBC.symm h3C
    have hEqZ :
        (A : ZMod 9) ^ 3 + (B : ZMod 9) ^ 5 = (C : ZMod 9) ^ 7 := by
      simpa only [Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ => (n : ZMod 9)) hEq
    have hABZ : (A : ZMod 9) ^ 3 + (B : ZMod 9) ^ 5 = 0 := by
      rw [seventh_cast_eq_zero_mod9_of_three_dvd h3C] at hEqZ
      exact hEqZ
    rcases mod9_cubic_plus_fifth_units _ _
      (isUnit_zmod9_of_not_three_dvd h3A)
      (isUnit_zmod9_of_not_three_dvd h3B) hABZ with hB | hB
    · left
      exact (ZMod.natCast_eq_natCast_iff' B 1 9).mp (by simpa using hB)
    · right
      exact (ZMod.natCast_eq_natCast_iff' B 8 9).mp (by simpa using hB)

/-- Convenience form of the strongest scanned relation when the fifth-power
base is divisible by three. -/
theorem signature357_mod243_of_three_dvd_B {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (hBC : Nat.Coprime B C) (h3B : 3 ∣ B)
    (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    C % 243 = A ^ 93 % 243 :=
  (signature357_three_adic_branch_table hAB hAC hBC hEq).2.1 h3B

/-- Convenience form of the strongest scanned relation when the
seventh-power base is divisible by three. -/
theorem signature357_mod243_of_three_dvd_C {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (hBC : Nat.Coprime B C) (h3C : 3 ∣ C)
    (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    (B + A ^ 33) % 243 = 0 :=
  (signature357_three_adic_branch_table hAB hAC hBC hEq).2.2 h3C


end BealRegular.Signature357CompositeLocal
