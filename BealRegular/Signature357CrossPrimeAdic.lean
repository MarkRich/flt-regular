import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Cross-prime-adic restrictions for signature `(3,5,7)`

This file treats two assumed divisibility placements:

* `5 ∣ B` makes `B^5` vanish modulo `5^5` and forces
  `C = A^1429 (mod 3125)`;
* `7 ∣ C` makes `C^7` vanish modulo `7^7` and forces
  `B = -A^423537 (mod 823543)`.

The latter also makes `B` a fourteenth root of unity modulo `49`, leaving
fourteen explicit residue classes.  These are conditional necessary
restrictions: the file neither derives nor excludes either divisibility branch
and does not prove nonexistence of `(3,5,7)` solutions.
-/

namespace BealRegular.Signature357CrossPrimeAdic

private theorem not_prime_dvd_right_of_coprime_of_dvd_left
    {p x y : ℕ} (hp : Nat.Prime p) (hxy : Nat.Coprime x y)
    (hx : p ∣ x) : ¬p ∣ y := by
  have hpy : Nat.Coprime p y := Nat.Coprime.of_dvd_left hx hxy
  exact hp.coprime_iff_not_dvd.mp hpy

private theorem isUnit_zmod3125_of_not_five_dvd {n : ℕ}
    (hn : ¬5 ∣ n) : IsUnit (n : ZMod 3125) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 3125 = 5 ^ 5 by norm_num] using
    (by decide : Nat.Prime 5).coprime_pow_of_not_dvd hn (m := 5)

private theorem mod3125_unit_pow_2500 {a : ZMod 3125}
    (ha : IsUnit a) : a ^ 2500 = 1 := by
  let u : (ZMod 3125)ˣ := ha.unit
  have hu : u ^ Nat.totient 3125 = 1 := ZMod.pow_totient u
  have hv := congrArg (fun x : (ZMod 3125)ˣ ↦ (x : ZMod 3125)) hu
  have htot : Nat.totient 3125 = 2500 := by
    rw [show 3125 = 5 ^ 5 by norm_num]
    rw [Nat.totient_prime_pow (by decide : Nat.Prime 5)
      (by norm_num : 0 < 5)]
    norm_num
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, htot, u,
    IsUnit.unit_spec] using hv

private theorem fifth_cast_eq_zero_mod3125_of_five_dvd {n : ℕ}
    (hn : 5 ∣ n) : (n : ZMod 3125) ^ 5 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  refine ⟨k ^ 5, ?_⟩
  ring

/-- If the fifth-power base is divisible by five, the two remaining bases
satisfy `C = A^1429 (mod 5^5)`. -/
theorem signature357_mod3125_of_five_dvd_B {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hBC : Nat.Coprime B C)
    (h5B : 5 ∣ B) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    C % 3125 = A ^ 1429 % 3125 := by
  have h5A : ¬5 ∣ A :=
    not_prime_dvd_right_of_coprime_of_dvd_left
      (by decide : Nat.Prime 5) hAB.symm h5B
  have h5C : ¬5 ∣ C :=
    not_prime_dvd_right_of_coprime_of_dvd_left
      (by decide : Nat.Prime 5) hBC h5B
  have hAUnit : IsUnit (A : ZMod 3125) :=
    isUnit_zmod3125_of_not_five_dvd h5A
  have hCUnit : IsUnit (C : ZMod 3125) :=
    isUnit_zmod3125_of_not_five_dvd h5C
  have hEqZ :
      (A : ZMod 3125) ^ 3 + (B : ZMod 3125) ^ 5 =
        (C : ZMod 3125) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ ↦ (n : ZMod 3125)) hEq
  have hUnits : (A : ZMod 3125) ^ 3 = (C : ZMod 3125) ^ 7 := by
    rw [fifth_cast_eq_zero_mod3125_of_five_dvd h5B, add_zero] at hEqZ
    exact hEqZ
  have hRaised : (A : ZMod 3125) ^ 6429 = (C : ZMod 3125) ^ 15001 := by
    calc
      (A : ZMod 3125) ^ 6429 = ((A : ZMod 3125) ^ 3) ^ 2143 := by
        simpa using (pow_mul (A : ZMod 3125) 3 2143)
      _ = ((C : ZMod 3125) ^ 7) ^ 2143 := by rw [hUnits]
      _ = (C : ZMod 3125) ^ 15001 := by
        simpa using (pow_mul (C : ZMod 3125) 7 2143).symm
  have hA2500 : (A : ZMod 3125) ^ 2500 = 1 :=
    mod3125_unit_pow_2500 hAUnit
  have hC2500 : (C : ZMod 3125) ^ 2500 = 1 :=
    mod3125_unit_pow_2500 hCUnit
  have hZ : (C : ZMod 3125) = (A : ZMod 3125) ^ 1429 := by
    calc
      (C : ZMod 3125) = (C : ZMod 3125) ^ 15001 := by
        rw [show 15001 = 2500 * 6 + 1 by norm_num, pow_add, pow_mul,
          hC2500]
        simp
      _ = (A : ZMod 3125) ^ 6429 := hRaised.symm
      _ = (A : ZMod 3125) ^ 1429 := by
        rw [show 6429 = 2500 * 2 + 1429 by norm_num, pow_add, pow_mul,
          hA2500]
        simp
  have hZ' : (C : ZMod 3125) = (A ^ 1429 : ℕ) := by
    simpa only [Nat.cast_pow] using hZ
  exact (ZMod.natCast_eq_natCast_iff' C (A ^ 1429) 3125).mp hZ'

private theorem isUnit_zmod823543_of_not_seven_dvd {n : ℕ}
    (hn : ¬7 ∣ n) : IsUnit (n : ZMod 823543) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 823543 = 7 ^ 7 by norm_num] using
    (by decide : Nat.Prime 7).coprime_pow_of_not_dvd hn (m := 7)

private theorem isUnit_zmod49_of_not_seven_dvd {n : ℕ}
    (hn : ¬7 ∣ n) : IsUnit (n : ZMod 49) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 49 = 7 ^ 2 by norm_num] using
    (by decide : Nat.Prime 7).coprime_pow_of_not_dvd hn (m := 2)

private theorem mod823543_unit_pow_705894 {a : ZMod 823543}
    (ha : IsUnit a) : a ^ 705894 = 1 := by
  let u : (ZMod 823543)ˣ := ha.unit
  have hu : u ^ Nat.totient 823543 = 1 := ZMod.pow_totient u
  have hv := congrArg (fun x : (ZMod 823543)ˣ ↦ (x : ZMod 823543)) hu
  have htot : Nat.totient 823543 = 705894 := by
    rw [show 823543 = 7 ^ 7 by norm_num]
    rw [Nat.totient_prime_pow (by decide : Nat.Prime 7)
      (by norm_num : 0 < 7)]
    norm_num
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, htot, u,
    IsUnit.unit_spec] using hv

private theorem mod49_unit_pow_42 {a : ZMod 49}
    (ha : IsUnit a) : a ^ 42 = 1 := by
  let u : (ZMod 49)ˣ := ha.unit
  have hu : u ^ Nat.totient 49 = 1 := ZMod.pow_totient u
  have hv := congrArg (fun x : (ZMod 49)ˣ ↦ (x : ZMod 49)) hu
  have htot : Nat.totient 49 = 42 := by
    rw [show 49 = 7 ^ 2 by norm_num]
    rw [Nat.totient_prime_pow (by decide : Nat.Prime 7)
      (by norm_num : 0 < 2)]
    norm_num
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, htot, u,
    IsUnit.unit_spec] using hv

private theorem seventh_cast_eq_zero_mod823543_of_seven_dvd {n : ℕ}
    (hn : 7 ∣ n) : (n : ZMod 823543) ^ 7 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  refine ⟨k ^ 7, ?_⟩
  ring

private theorem seventh_cast_eq_zero_mod49_of_seven_dvd {n : ℕ}
    (hn : 7 ∣ n) : (n : ZMod 49) ^ 7 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  refine ⟨7 ^ 5 * k ^ 7, ?_⟩
  ring

/-- If the seventh-power base is divisible by seven, then
`B = -A^423537 (mod 7^7)`. -/
theorem signature357_mod823543_of_seven_dvd_C {A B C : ℕ}
    (hAC : Nat.Coprime A C) (hBC : Nat.Coprime B C)
    (h7C : 7 ∣ C) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    (B + A ^ 423537) % 823543 = 0 := by
  have h7A : ¬7 ∣ A :=
    not_prime_dvd_right_of_coprime_of_dvd_left
      (by decide : Nat.Prime 7) hAC.symm h7C
  have h7B : ¬7 ∣ B :=
    not_prime_dvd_right_of_coprime_of_dvd_left
      (by decide : Nat.Prime 7) hBC.symm h7C
  have hAUnit : IsUnit (A : ZMod 823543) :=
    isUnit_zmod823543_of_not_seven_dvd h7A
  have hBUnit : IsUnit (B : ZMod 823543) :=
    isUnit_zmod823543_of_not_seven_dvd h7B
  have hEqZ :
      (A : ZMod 823543) ^ 3 + (B : ZMod 823543) ^ 5 =
        (C : ZMod 823543) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ ↦ (n : ZMod 823543)) hEq
  have hZero :
      (A : ZMod 823543) ^ 3 + (B : ZMod 823543) ^ 5 = 0 := by
    rw [seventh_cast_eq_zero_mod823543_of_seven_dvd h7C] at hEqZ
    exact hEqZ
  have hUnits :
      (A : ZMod 823543) ^ 3 = (-(B : ZMod 823543)) ^ 5 := by
    rw [(by decide : Odd 5).neg_pow]
    exact eq_neg_of_add_eq_zero_left hZero
  have hNegBUnit : IsUnit (-(B : ZMod 823543)) := hBUnit.neg
  have hRaised :
      (A : ZMod 823543) ^ 423537 =
        (-(B : ZMod 823543)) ^ 705895 := by
    calc
      (A : ZMod 823543) ^ 423537 =
          ((A : ZMod 823543) ^ 3) ^ 141179 := by
        simpa using (pow_mul (A : ZMod 823543) 3 141179)
      _ = ((-(B : ZMod 823543)) ^ 5) ^ 141179 := by rw [hUnits]
      _ = (-(B : ZMod 823543)) ^ 705895 := by
        simpa using (pow_mul (-(B : ZMod 823543)) 5 141179).symm
  have hNegBEuler :
      (-(B : ZMod 823543)) ^ 705894 = 1 :=
    mod823543_unit_pow_705894 hNegBUnit
  have hANegB :
      (A : ZMod 823543) ^ 423537 = -(B : ZMod 823543) := by
    rw [show 705895 = 705894 + 1 by norm_num, pow_add, hNegBEuler] at hRaised
    simpa using hRaised
  have hSum :
      (B : ZMod 823543) + (A : ZMod 823543) ^ 423537 = 0 := by
    calc
      (B : ZMod 823543) + (A : ZMod 823543) ^ 423537 =
          (B : ZMod 823543) + (-(B : ZMod 823543)) :=
        congrArg (fun x : ZMod 823543 ↦ (B : ZMod 823543) + x) hANegB
      _ = 0 := add_neg_cancel (B : ZMod 823543)
  have hCast : ((B + A ^ 423537 : ℕ) : ZMod 823543) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_zero] using hSum
  exact Nat.dvd_iff_mod_eq_zero.mp
    ((ZMod.natCast_eq_zero_iff (B + A ^ 423537) 823543).mp hCast)

private theorem signature357_zmod49_fourteenthRoot_of_seven_dvd_C
    {A B C : ℕ}
    (hAC : Nat.Coprime A C) (hBC : Nat.Coprime B C)
    (h7C : 7 ∣ C) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    (B : ZMod 49) ^ 14 = 1 := by
  have h7A : ¬7 ∣ A :=
    not_prime_dvd_right_of_coprime_of_dvd_left
      (by decide : Nat.Prime 7) hAC.symm h7C
  have h7B : ¬7 ∣ B :=
    not_prime_dvd_right_of_coprime_of_dvd_left
      (by decide : Nat.Prime 7) hBC.symm h7C
  have hAUnit : IsUnit (A : ZMod 49) :=
    isUnit_zmod49_of_not_seven_dvd h7A
  have hBUnit : IsUnit (B : ZMod 49) :=
    isUnit_zmod49_of_not_seven_dvd h7B
  have hEqZ :
      (A : ZMod 49) ^ 3 + (B : ZMod 49) ^ 5 =
        (C : ZMod 49) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ ↦ (n : ZMod 49)) hEq
  have hZero : (A : ZMod 49) ^ 3 + (B : ZMod 49) ^ 5 = 0 := by
    rw [seventh_cast_eq_zero_mod49_of_seven_dvd h7C] at hEqZ
    exact hEqZ
  have hUnits : (A : ZMod 49) ^ 3 = (-(B : ZMod 49)) ^ 5 := by
    rw [(by decide : Odd 5).neg_pow]
    exact eq_neg_of_add_eq_zero_left hZero
  have hNegBUnit : IsUnit (-(B : ZMod 49)) := hBUnit.neg
  have hA42 : (A : ZMod 49) ^ 42 = 1 := mod49_unit_pow_42 hAUnit
  have hNegB42 : (-(B : ZMod 49)) ^ 42 = 1 :=
    mod49_unit_pow_42 hNegBUnit
  have hRaised : (A : ZMod 49) ^ 51 = (-(B : ZMod 49)) ^ 85 := by
    calc
      (A : ZMod 49) ^ 51 = ((A : ZMod 49) ^ 3) ^ 17 := by
        simpa using (pow_mul (A : ZMod 49) 3 17)
      _ = ((-(B : ZMod 49)) ^ 5) ^ 17 := by rw [hUnits]
      _ = (-(B : ZMod 49)) ^ 85 := by
        simpa using (pow_mul (-(B : ZMod 49)) 5 17).symm
  have hNegB84 : (-(B : ZMod 49)) ^ 84 = 1 := by
    calc
      (-(B : ZMod 49)) ^ 84 = ((-(B : ZMod 49)) ^ 42) ^ 2 := by
        simpa using (pow_mul (-(B : ZMod 49)) 42 2)
      _ = 1 := by rw [hNegB42]; norm_num
  have hANegB : (A : ZMod 49) ^ 9 = -(B : ZMod 49) := by
    calc
      (A : ZMod 49) ^ 9 = (A : ZMod 49) ^ 51 := by
        rw [show 51 = 42 + 9 by norm_num, pow_add, hA42]
        simp
      _ = (-(B : ZMod 49)) ^ 85 := hRaised
      _ = -(B : ZMod 49) := by
        rw [show 85 = 84 + 1 by norm_num, pow_add, hNegB84]
        simp
  calc
    (B : ZMod 49) ^ 14 = (-(B : ZMod 49)) ^ 14 := by
      rw [(by decide : Even 14).neg_pow]
    _ = ((A : ZMod 49) ^ 9) ^ 14 := by rw [hANegB]
    _ = (A : ZMod 49) ^ 126 := by
      simpa using (pow_mul (A : ZMod 49) 9 14).symm
    _ = ((A : ZMod 49) ^ 42) ^ 3 := by
      simpa using (pow_mul (A : ZMod 49) 42 3)
    _ = 1 := by rw [hA42]; norm_num

/-- In the `7 ∣ C` branch, `B` is a fourteenth root of unity modulo `49`. -/
theorem signature357_mod49_fourteenthRoot_of_seven_dvd_C {A B C : ℕ}
    (hAC : Nat.Coprime A C) (hBC : Nat.Coprime B C)
    (h7C : 7 ∣ C) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    B ^ 14 % 49 = 1 := by
  have hZ :=
    signature357_zmod49_fourteenthRoot_of_seven_dvd_C hAC hBC h7C hEq
  have hCast : ((B ^ 14 : ℕ) : ZMod 49) = (1 : ℕ) := by
    simpa only [Nat.cast_pow, Nat.cast_one] using hZ
  have hMod := (ZMod.natCast_eq_natCast_iff' (B ^ 14) 1 49).mp hCast
  simpa using hMod

/-- The fourteen explicit residues in the preceding root-of-unity
condition. -/
theorem signature357_mod49_residues_of_seven_dvd_C {A B C : ℕ}
    (hAC : Nat.Coprime A C) (hBC : Nat.Coprime B C)
    (h7C : 7 ∣ C) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    B % 49 = 1 ∨ B % 49 = 6 ∨ B % 49 = 8 ∨ B % 49 = 13 ∨
      B % 49 = 15 ∨ B % 49 = 20 ∨ B % 49 = 22 ∨ B % 49 = 27 ∨
      B % 49 = 29 ∨ B % 49 = 34 ∨ B % 49 = 36 ∨ B % 49 = 41 ∨
      B % 49 = 43 ∨ B % 49 = 48 := by
  have hFourteenth :=
    signature357_mod49_fourteenthRoot_of_seven_dvd_C hAC hBC h7C hEq
  let r := B % 49
  have hr : r < 49 := Nat.mod_lt B (by norm_num)
  have hrFourteenth : r ^ 14 % 49 = 1 := by
    simpa only [r, ← Nat.pow_mod] using hFourteenth
  change r = 1 ∨ r = 6 ∨ r = 8 ∨ r = 13 ∨ r = 15 ∨ r = 20 ∨
    r = 22 ∨ r = 27 ∨ r = 29 ∨ r = 34 ∨ r = 36 ∨ r = 41 ∨
    r = 43 ∨ r = 48
  interval_cases r <;> norm_num at hrFourteenth
  all_goals norm_num


end BealRegular.Signature357CrossPrimeAdic
