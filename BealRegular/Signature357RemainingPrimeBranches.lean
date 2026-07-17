import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Remaining prime-divisibility branches for signature `(3,5,7)`

This file proves necessary restrictions in two assumed branches:

* `5 ∣ A` forces `C = B^15 (mod 125)`;
* `7 ∣ B` forces `A^6 = 1` and `C^14 = 1 (mod 49)`.

The corresponding residue sets modulo 25 and 49 are made explicit.  Neither
divisibility placement is derived or excluded, and the results do not prove
nonexistence of `(3,5,7)` solutions.
-/

namespace BealRegular.Signature357RemainingPrimeBranches

private theorem not_prime_dvd_right_of_coprime_of_dvd_left
    {p x y : ℕ} (hp : Nat.Prime p) (hxy : Nat.Coprime x y)
    (hx : p ∣ x) : ¬p ∣ y := by
  have hpy : Nat.Coprime p y := Nat.Coprime.of_dvd_left hx hxy
  exact hp.coprime_iff_not_dvd.mp hpy

private theorem isUnit_zmod125_of_not_five_dvd {n : ℕ}
    (hn : ¬5 ∣ n) : IsUnit (n : ZMod 125) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 125 = 5 ^ 3 by norm_num] using
    (by decide : Nat.Prime 5).coprime_pow_of_not_dvd hn (m := 3)

private theorem mod125_unit_pow_100 {a : ZMod 125}
    (ha : IsUnit a) : a ^ 100 = 1 := by
  let u : (ZMod 125)ˣ := ha.unit
  have hu : u ^ Nat.totient 125 = 1 := ZMod.pow_totient u
  have hv := congrArg (fun x : (ZMod 125)ˣ => (x : ZMod 125)) hu
  have htot : Nat.totient 125 = 100 := by
    rw [show 125 = 5 ^ 3 by norm_num]
    rw [Nat.totient_prime_pow (by decide : Nat.Prime 5)
      (by norm_num : 0 < 3)]
    norm_num
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, htot, u,
    IsUnit.unit_spec] using hv

private theorem cube_cast_eq_zero_mod125_of_five_dvd {n : ℕ}
    (hn : 5 ∣ n) : (n : ZMod 125) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  use k ^ 3
  ring

/-- In the `5 ∣ A` branch, `C = B^15 (mod 5^3)`. -/
theorem signature357_mod125_of_five_dvd_A {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (h5A : 5 ∣ A) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    C % 125 = B ^ 15 % 125 := by
  have h5B : ¬5 ∣ B :=
    not_prime_dvd_right_of_coprime_of_dvd_left
      (by decide : Nat.Prime 5) hAB h5A
  have h5C : ¬5 ∣ C :=
    not_prime_dvd_right_of_coprime_of_dvd_left
      (by decide : Nat.Prime 5) hAC h5A
  have hBUnit : IsUnit (B : ZMod 125) :=
    isUnit_zmod125_of_not_five_dvd h5B
  have hCUnit : IsUnit (C : ZMod 125) :=
    isUnit_zmod125_of_not_five_dvd h5C
  have hEqZ :
      (A : ZMod 125) ^ 3 + (B : ZMod 125) ^ 5 =
        (C : ZMod 125) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ZMod 125)) hEq
  have hUnits : (B : ZMod 125) ^ 5 = (C : ZMod 125) ^ 7 := by
    rw [cube_cast_eq_zero_mod125_of_five_dvd h5A, zero_add] at hEqZ
    exact hEqZ
  have hRaised : (B : ZMod 125) ^ 215 = (C : ZMod 125) ^ 301 := by
    calc
      (B : ZMod 125) ^ 215 = ((B : ZMod 125) ^ 5) ^ 43 := by
        simpa using (pow_mul (B : ZMod 125) 5 43)
      _ = ((C : ZMod 125) ^ 7) ^ 43 := by rw [hUnits]
      _ = (C : ZMod 125) ^ 301 := by
        simpa using (pow_mul (C : ZMod 125) 7 43).symm
  have hB100 : (B : ZMod 125) ^ 100 = 1 := mod125_unit_pow_100 hBUnit
  have hC100 : (C : ZMod 125) ^ 100 = 1 := mod125_unit_pow_100 hCUnit
  have hZ : (C : ZMod 125) = (B : ZMod 125) ^ 15 := by
    calc
      (C : ZMod 125) = (C : ZMod 125) ^ 301 := by
        rw [show 301 = 100 * 3 + 1 by norm_num, pow_add, pow_mul, hC100]
        simp
      _ = (B : ZMod 125) ^ 215 := hRaised.symm
      _ = (B : ZMod 125) ^ 15 := by
        rw [show 215 = 100 * 2 + 15 by norm_num, pow_add, pow_mul, hB100]
        simp
  have hZ' : (C : ZMod 125) = (B ^ 15 : ℕ) := by
    simpa only [Nat.cast_pow] using hZ
  exact (ZMod.natCast_eq_natCast_iff' C (B ^ 15) 125).mp hZ'

private theorem isUnit_zmod25_of_not_five_dvd {n : ℕ}
    (hn : ¬5 ∣ n) : IsUnit (n : ZMod 25) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 25 = 5 ^ 2 by norm_num] using
    (by decide : Nat.Prime 5).coprime_pow_of_not_dvd hn (m := 2)

private theorem mod25_unit_pow_20 {a : ZMod 25}
    (ha : IsUnit a) : a ^ 20 = 1 := by
  let u : (ZMod 25)ˣ := ha.unit
  have hu : u ^ Nat.totient 25 = 1 := ZMod.pow_totient u
  have hv := congrArg (fun x : (ZMod 25)ˣ => (x : ZMod 25)) hu
  have htot : Nat.totient 25 = 20 := by
    rw [show 25 = 5 ^ 2 by norm_num]
    rw [Nat.totient_prime_pow (by decide : Nat.Prime 5)
      (by norm_num : 0 < 2)]
    norm_num
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, htot, u,
    IsUnit.unit_spec] using hv

private theorem cube_cast_eq_zero_mod25_of_five_dvd {n : ℕ}
    (hn : 5 ∣ n) : (n : ZMod 25) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  use 5 * k ^ 3
  ring

private theorem signature357_zmod25_fourthRoot_of_five_dvd_A
    {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (h5A : 5 ∣ A) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    (C : ZMod 25) ^ 4 = 1 := by
  have h5B : ¬5 ∣ B :=
    not_prime_dvd_right_of_coprime_of_dvd_left
      (by decide : Nat.Prime 5) hAB h5A
  have h5C : ¬5 ∣ C :=
    not_prime_dvd_right_of_coprime_of_dvd_left
      (by decide : Nat.Prime 5) hAC h5A
  have hBUnit : IsUnit (B : ZMod 25) :=
    isUnit_zmod25_of_not_five_dvd h5B
  have hCUnit : IsUnit (C : ZMod 25) :=
    isUnit_zmod25_of_not_five_dvd h5C
  have hEqZ :
      (A : ZMod 25) ^ 3 + (B : ZMod 25) ^ 5 =
        (C : ZMod 25) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ZMod 25)) hEq
  have hUnits : (B : ZMod 25) ^ 5 = (C : ZMod 25) ^ 7 := by
    rw [cube_cast_eq_zero_mod25_of_five_dvd h5A, zero_add] at hEqZ
    exact hEqZ
  have hC20 : (C : ZMod 25) ^ 20 = 1 := mod25_unit_pow_20 hCUnit
  have hPair : (C : ZMod 25) = (B : ZMod 25) ^ 15 := by
    have hRaised : (B : ZMod 25) ^ 15 = (C : ZMod 25) ^ 21 := by
      calc
        (B : ZMod 25) ^ 15 = ((B : ZMod 25) ^ 5) ^ 3 := by
          simpa using (pow_mul (B : ZMod 25) 5 3)
        _ = ((C : ZMod 25) ^ 7) ^ 3 := by rw [hUnits]
        _ = (C : ZMod 25) ^ 21 := by
          simpa using (pow_mul (C : ZMod 25) 7 3).symm
    rw [show 21 = 20 + 1 by norm_num, pow_add, hC20] at hRaised
    simpa using hRaised.symm
  have hB20 : (B : ZMod 25) ^ 20 = 1 := mod25_unit_pow_20 hBUnit
  calc
    (C : ZMod 25) ^ 4 = ((B : ZMod 25) ^ 15) ^ 4 := by rw [hPair]
    _ = (B : ZMod 25) ^ 60 := by
      simpa using (pow_mul (B : ZMod 25) 15 4).symm
    _ = ((B : ZMod 25) ^ 20) ^ 3 := by
      simpa using (pow_mul (B : ZMod 25) 20 3)
    _ = 1 := by rw [hB20]; norm_num

/-- Explicit small-modulus consequence of `5 ∣ A`. -/
theorem signature357_mod25_C_residues_of_five_dvd_A {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (h5A : 5 ∣ A) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    C % 25 = 1 ∨ C % 25 = 7 ∨ C % 25 = 18 ∨ C % 25 = 24 := by
  have hRoot :=
    signature357_zmod25_fourthRoot_of_five_dvd_A hAB hAC h5A hEq
  have hCast : ((C ^ 4 : ℕ) : ZMod 25) = (1 : ℕ) := by
    simpa only [Nat.cast_pow, Nat.cast_one] using hRoot
  have hFourth : C ^ 4 % 25 = 1 := by
    have hMod := (ZMod.natCast_eq_natCast_iff' (C ^ 4) 1 25).mp hCast
    simpa using hMod
  let r := C % 25
  have hr : r < 25 := Nat.mod_lt C (by norm_num)
  have hrFourth : r ^ 4 % 25 = 1 := by
    simpa only [r, ← Nat.pow_mod] using hFourth
  change r = 1 ∨ r = 7 ∨ r = 18 ∨ r = 24
  interval_cases r <;> norm_num at hrFourth
  all_goals norm_num

private theorem isUnit_zmod49_of_not_seven_dvd {n : ℕ}
    (hn : ¬7 ∣ n) : IsUnit (n : ZMod 49) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 49 = 7 ^ 2 by norm_num] using
    (by decide : Nat.Prime 7).coprime_pow_of_not_dvd hn (m := 2)

private theorem mod49_unit_pow_42 {a : ZMod 49}
    (ha : IsUnit a) : a ^ 42 = 1 := by
  let u : (ZMod 49)ˣ := ha.unit
  have hu : u ^ Nat.totient 49 = 1 := ZMod.pow_totient u
  have hv := congrArg (fun x : (ZMod 49)ˣ => (x : ZMod 49)) hu
  have htot : Nat.totient 49 = 42 := by
    rw [show 49 = 7 ^ 2 by norm_num]
    rw [Nat.totient_prime_pow (by decide : Nat.Prime 7)
      (by norm_num : 0 < 2)]
    norm_num
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, htot, u,
    IsUnit.unit_spec] using hv

private theorem fifth_cast_eq_zero_mod49_of_seven_dvd {n : ℕ}
    (hn : 7 ∣ n) : (n : ZMod 49) ^ 5 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  use 7 ^ 3 * k ^ 5
  ring

private theorem signature357_zmod49_roots_of_seven_dvd_B {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hBC : Nat.Coprime B C)
    (h7B : 7 ∣ B) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    (A : ZMod 49) ^ 6 = 1 ∧ (C : ZMod 49) ^ 14 = 1 := by
  have h7A : ¬7 ∣ A :=
    not_prime_dvd_right_of_coprime_of_dvd_left
      (by decide : Nat.Prime 7) hAB.symm h7B
  have h7C : ¬7 ∣ C :=
    not_prime_dvd_right_of_coprime_of_dvd_left
      (by decide : Nat.Prime 7) hBC h7B
  have hAUnit : IsUnit (A : ZMod 49) :=
    isUnit_zmod49_of_not_seven_dvd h7A
  have hCUnit : IsUnit (C : ZMod 49) :=
    isUnit_zmod49_of_not_seven_dvd h7C
  have hEqZ :
      (A : ZMod 49) ^ 3 + (B : ZMod 49) ^ 5 =
        (C : ZMod 49) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ZMod 49)) hEq
  have hUnits : (A : ZMod 49) ^ 3 = (C : ZMod 49) ^ 7 := by
    rw [fifth_cast_eq_zero_mod49_of_seven_dvd h7B, add_zero] at hEqZ
    exact hEqZ
  have hA42 : (A : ZMod 49) ^ 42 = 1 := mod49_unit_pow_42 hAUnit
  have hC42 : (C : ZMod 49) ^ 42 = 1 := mod49_unit_pow_42 hCUnit
  have hA18 : (A : ZMod 49) ^ 18 = 1 := by
    calc
      (A : ZMod 49) ^ 18 = ((A : ZMod 49) ^ 3) ^ 6 := by
        simpa using (pow_mul (A : ZMod 49) 3 6)
      _ = ((C : ZMod 49) ^ 7) ^ 6 := by rw [hUnits]
      _ = (C : ZMod 49) ^ 42 := by
        simpa using (pow_mul (C : ZMod 49) 7 6).symm
      _ = 1 := hC42
  have hA36 : (A : ZMod 49) ^ 36 = 1 := by
    calc
      (A : ZMod 49) ^ 36 = ((A : ZMod 49) ^ 18) ^ 2 := by
        simpa using (pow_mul (A : ZMod 49) 18 2)
      _ = 1 := by rw [hA18]; norm_num
  have hA6 : (A : ZMod 49) ^ 6 = 1 := by
    have hSplit : (A : ZMod 49) ^ 42 =
        (A : ZMod 49) ^ 36 * (A : ZMod 49) ^ 6 := by
      rw [← pow_add]
    rw [hSplit, hA36, one_mul] at hA42
    exact hA42
  have hC98 : (C : ZMod 49) ^ 98 = 1 := by
    calc
      (C : ZMod 49) ^ 98 = ((C : ZMod 49) ^ 7) ^ 14 := by
        simpa using (pow_mul (C : ZMod 49) 7 14)
      _ = ((A : ZMod 49) ^ 3) ^ 14 := by rw [hUnits]
      _ = (A : ZMod 49) ^ 42 := by
        simpa using (pow_mul (A : ZMod 49) 3 14).symm
      _ = 1 := hA42
  have hC84 : (C : ZMod 49) ^ 84 = 1 := by
    calc
      (C : ZMod 49) ^ 84 = ((C : ZMod 49) ^ 42) ^ 2 := by
        simpa using (pow_mul (C : ZMod 49) 42 2)
      _ = 1 := by rw [hC42]; norm_num
  have hC14 : (C : ZMod 49) ^ 14 = 1 := by
    have hSplit : (C : ZMod 49) ^ 98 =
        (C : ZMod 49) ^ 84 * (C : ZMod 49) ^ 14 := by
      rw [← pow_add]
    rw [hSplit, hC84, one_mul] at hC98
    exact hC98
  exact ⟨hA6, hC14⟩

/-- The two exact root-of-unity restrictions in the `7 ∣ B` branch. -/
theorem signature357_mod49_roots_of_seven_dvd_B {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hBC : Nat.Coprime B C)
    (h7B : 7 ∣ B) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    A ^ 6 % 49 = 1 ∧ C ^ 14 % 49 = 1 := by
  obtain ⟨hA, hC⟩ :=
    signature357_zmod49_roots_of_seven_dvd_B hAB hBC h7B hEq
  constructor
  · have hCast : ((A ^ 6 : ℕ) : ZMod 49) = (1 : ℕ) := by
      simpa only [Nat.cast_pow, Nat.cast_one] using hA
    have hMod := (ZMod.natCast_eq_natCast_iff' (A ^ 6) 1 49).mp hCast
    simpa using hMod
  · have hCast : ((C ^ 14 : ℕ) : ZMod 49) = (1 : ℕ) := by
      simpa only [Nat.cast_pow, Nat.cast_one] using hC
    have hMod := (ZMod.natCast_eq_natCast_iff' (C ^ 14) 1 49).mp hCast
    simpa using hMod

/-- Explicit coordinate residue sets in the `7 ∣ B` branch. -/
theorem signature357_mod49_residues_of_seven_dvd_B {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hBC : Nat.Coprime B C)
    (h7B : 7 ∣ B) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    (A % 49 = 1 ∨ A % 49 = 18 ∨ A % 49 = 19 ∨
      A % 49 = 30 ∨ A % 49 = 31 ∨ A % 49 = 48) ∧
    (C % 49 = 1 ∨ C % 49 = 6 ∨ C % 49 = 8 ∨ C % 49 = 13 ∨
      C % 49 = 15 ∨ C % 49 = 20 ∨ C % 49 = 22 ∨ C % 49 = 27 ∨
      C % 49 = 29 ∨ C % 49 = 34 ∨ C % 49 = 36 ∨ C % 49 = 41 ∨
      C % 49 = 43 ∨ C % 49 = 48) := by
  obtain ⟨hA, hC⟩ := signature357_mod49_roots_of_seven_dvd_B hAB hBC h7B hEq
  constructor
  · let r := A % 49
    have hr : r < 49 := Nat.mod_lt A (by norm_num)
    have hRoot : r ^ 6 % 49 = 1 := by
      simpa only [r, ← Nat.pow_mod] using hA
    change r = 1 ∨ r = 18 ∨ r = 19 ∨ r = 30 ∨ r = 31 ∨ r = 48
    interval_cases r <;> norm_num at hRoot
    all_goals norm_num
  · let r := C % 49
    have hr : r < 49 := Nat.mod_lt C (by norm_num)
    have hRoot : r ^ 14 % 49 = 1 := by
      simpa only [r, ← Nat.pow_mod] using hC
    change r = 1 ∨ r = 6 ∨ r = 8 ∨ r = 13 ∨ r = 15 ∨ r = 20 ∨
      r = 22 ∨ r = 27 ∨ r = 29 ∨ r = 34 ∨ r = 36 ∨ r = 41 ∨
      r = 43 ∨ r = 48
    interval_cases r <;> norm_num at hRoot
    all_goals norm_num


end BealRegular.Signature357RemainingPrimeBranches
