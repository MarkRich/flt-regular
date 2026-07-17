import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Seven-adic restrictions for signature `(3,5,7)`

For natural numbers satisfying

`A ^ 3 + B ^ 5 = C ^ 7`,

the branch `7 ∣ A` makes the cubic term vanish modulo `7 ^ 3 = 343`.
If `A` is coprime to both `B` and `C`, the other two bases are units, so
`B ^ 5 = C ^ 7`.  Euler-unit exponent arithmetic then gives

`B = C ^ 119 (mod 343)`.

Working modulo `49` also shows that `B` is a sixth root of unity.  Its six
possible residue classes are listed explicitly.  These are conditional
necessary restrictions: the file does not prove `7 ∣ A`, exclude that branch,
or prove nonexistence of `(3,5,7)` solutions.  No positivity or nonzero
hypothesis is assumed.
-/

namespace BealRegular.Signature357SevenAdic

private theorem not_seven_dvd_right_of_coprime_of_dvd_left
    {x y : ℕ} (hxy : Nat.Coprime x y) (hx : 7 ∣ x) : ¬7 ∣ y := by
  have h7y : Nat.Coprime 7 y := Nat.Coprime.of_dvd_left hx hxy
  exact (by decide : Nat.Prime 7).coprime_iff_not_dvd.mp h7y

private theorem isUnit_zmod343_of_not_seven_dvd {n : ℕ}
    (hn : ¬7 ∣ n) : IsUnit (n : ZMod 343) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 343 = 7 ^ 3 by norm_num] using
    (by decide : Nat.Prime 7).coprime_pow_of_not_dvd hn (m := 3)

private theorem isUnit_zmod49_of_not_seven_dvd {n : ℕ}
    (hn : ¬7 ∣ n) : IsUnit (n : ZMod 49) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 49 = 7 ^ 2 by norm_num] using
    (by decide : Nat.Prime 7).coprime_pow_of_not_dvd hn (m := 2)

private theorem mod343_unit_pow_294 {a : ZMod 343}
    (ha : IsUnit a) : a ^ 294 = 1 := by
  let u : (ZMod 343)ˣ := ha.unit
  have hu : u ^ Nat.totient 343 = 1 := ZMod.pow_totient u
  have hv := congrArg (fun x : (ZMod 343)ˣ ↦ (x : ZMod 343)) hu
  have htot : Nat.totient 343 = 294 := by
    rw [show 343 = 7 ^ 3 by norm_num]
    rw [Nat.totient_prime_pow (by decide : Nat.Prime 7)
      (by norm_num : 0 < 3)]
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

private theorem cube_cast_eq_zero_mod343_of_seven_dvd {n : ℕ}
    (hn : 7 ∣ n) : (n : ZMod 343) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  refine ⟨k ^ 3, ?_⟩
  ring

private theorem cube_cast_eq_zero_mod49_of_seven_dvd {n : ℕ}
    (hn : 7 ∣ n) : (n : ZMod 49) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  refine ⟨7 * k ^ 3, ?_⟩
  ring

private theorem signature357_zmod343_pair_of_seven_dvd_A {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (h7A : 7 ∣ A) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    (B : ZMod 343) = (C : ZMod 343) ^ 119 := by
  have h7B : ¬7 ∣ B :=
    not_seven_dvd_right_of_coprime_of_dvd_left hAB h7A
  have h7C : ¬7 ∣ C :=
    not_seven_dvd_right_of_coprime_of_dvd_left hAC h7A
  have hBUnit : IsUnit (B : ZMod 343) :=
    isUnit_zmod343_of_not_seven_dvd h7B
  have hCUnit : IsUnit (C : ZMod 343) :=
    isUnit_zmod343_of_not_seven_dvd h7C
  have hEqZ :
      (A : ZMod 343) ^ 3 + (B : ZMod 343) ^ 5 =
        (C : ZMod 343) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ ↦ (n : ZMod 343)) hEq
  have hUnits : (B : ZMod 343) ^ 5 = (C : ZMod 343) ^ 7 := by
    rw [cube_cast_eq_zero_mod343_of_seven_dvd h7A, zero_add] at hEqZ
    exact hEqZ
  have hRaised : (B : ZMod 343) ^ 295 = (C : ZMod 343) ^ 413 := by
    calc
      (B : ZMod 343) ^ 295 = ((B : ZMod 343) ^ 5) ^ 59 := by
        simpa using (pow_mul (B : ZMod 343) 5 59)
      _ = ((C : ZMod 343) ^ 7) ^ 59 := by rw [hUnits]
      _ = (C : ZMod 343) ^ 413 := by
        simpa using (pow_mul (C : ZMod 343) 7 59).symm
  have hB294 : (B : ZMod 343) ^ 294 = 1 :=
    mod343_unit_pow_294 hBUnit
  have hC294 : (C : ZMod 343) ^ 294 = 1 :=
    mod343_unit_pow_294 hCUnit
  calc
    (B : ZMod 343) = (B : ZMod 343) ^ 295 := by
      rw [show 295 = 294 + 1 by norm_num, pow_add, hB294]
      simp
    _ = (C : ZMod 343) ^ 413 := hRaised
    _ = (C : ZMod 343) ^ 119 := by
      rw [show 413 = 294 + 119 by norm_num, pow_add, hC294]
      simp

/-- If the cubic base is divisible by seven, the remaining two bases satisfy
the exact pair relation `B = C^119 (mod 7^3)`. -/
theorem signature357_mod343_of_seven_dvd_A {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (h7A : 7 ∣ A) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    B % 343 = C ^ 119 % 343 := by
  have hZ := signature357_zmod343_pair_of_seven_dvd_A hAB hAC h7A hEq
  have hZ' : (B : ZMod 343) = (C ^ 119 : ℕ) := by
    simpa only [Nat.cast_pow] using hZ
  exact (ZMod.natCast_eq_natCast_iff' B (C ^ 119) 343).mp hZ'

private theorem signature357_zmod49_sixthRoot_of_seven_dvd_A {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (h7A : 7 ∣ A) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    (B : ZMod 49) ^ 6 = 1 := by
  have h7B : ¬7 ∣ B :=
    not_seven_dvd_right_of_coprime_of_dvd_left hAB h7A
  have h7C : ¬7 ∣ C :=
    not_seven_dvd_right_of_coprime_of_dvd_left hAC h7A
  have hBUnit : IsUnit (B : ZMod 49) :=
    isUnit_zmod49_of_not_seven_dvd h7B
  have hCUnit : IsUnit (C : ZMod 49) :=
    isUnit_zmod49_of_not_seven_dvd h7C
  have hEqZ :
      (A : ZMod 49) ^ 3 + (B : ZMod 49) ^ 5 =
        (C : ZMod 49) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ ↦ (n : ZMod 49)) hEq
  have hUnits : (B : ZMod 49) ^ 5 = (C : ZMod 49) ^ 7 := by
    rw [cube_cast_eq_zero_mod49_of_seven_dvd h7A, zero_add] at hEqZ
    exact hEqZ
  have hRaised : (B : ZMod 49) ^ 85 = (C : ZMod 49) ^ 119 := by
    calc
      (B : ZMod 49) ^ 85 = ((B : ZMod 49) ^ 5) ^ 17 := by
        simpa using (pow_mul (B : ZMod 49) 5 17)
      _ = ((C : ZMod 49) ^ 7) ^ 17 := by rw [hUnits]
      _ = (C : ZMod 49) ^ 119 := by
        simpa using (pow_mul (C : ZMod 49) 7 17).symm
  have hB42 : (B : ZMod 49) ^ 42 = 1 := mod49_unit_pow_42 hBUnit
  have hC42 : (C : ZMod 49) ^ 42 = 1 := mod49_unit_pow_42 hCUnit
  have hB84 : (B : ZMod 49) ^ 84 = 1 := by
    calc
      (B : ZMod 49) ^ 84 = ((B : ZMod 49) ^ 42) ^ 2 := by
        simpa using (pow_mul (B : ZMod 49) 42 2)
      _ = 1 := by rw [hB42]; norm_num
  have hC84 : (C : ZMod 49) ^ 84 = 1 := by
    calc
      (C : ZMod 49) ^ 84 = ((C : ZMod 49) ^ 42) ^ 2 := by
        simpa using (pow_mul (C : ZMod 49) 42 2)
      _ = 1 := by rw [hC42]; norm_num
  have hBC35 : (B : ZMod 49) = (C : ZMod 49) ^ 35 := by
    calc
      (B : ZMod 49) = (B : ZMod 49) ^ 85 := by
        rw [show 85 = 84 + 1 by norm_num, pow_add, hB84]
        simp
      _ = (C : ZMod 49) ^ 119 := hRaised
      _ = (C : ZMod 49) ^ 35 := by
        rw [show 119 = 84 + 35 by norm_num, pow_add, hC84]
        simp
  calc
    (B : ZMod 49) ^ 6 = ((C : ZMod 49) ^ 35) ^ 6 := by rw [hBC35]
    _ = (C : ZMod 49) ^ 210 := by
      simpa using (pow_mul (C : ZMod 49) 35 6).symm
    _ = ((C : ZMod 49) ^ 42) ^ 5 := by
      simpa using (pow_mul (C : ZMod 49) 42 5)
    _ = 1 := by rw [hC42]; norm_num

/-- In the same seven-divisibility branch, the fifth-power base is a sixth
root of unity modulo `49`. -/
theorem signature357_mod49_sixthRoot_of_seven_dvd_A {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (h7A : 7 ∣ A) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    B ^ 6 % 49 = 1 := by
  have hZ := signature357_zmod49_sixthRoot_of_seven_dvd_A hAB hAC h7A hEq
  have hCast : ((B ^ 6 : ℕ) : ZMod 49) = (1 : ℕ) := by
    simpa only [Nat.cast_pow, Nat.cast_one] using hZ
  have hMod := (ZMod.natCast_eq_natCast_iff' (B ^ 6) 1 49).mp hCast
  simpa using hMod

/-- The six explicit residue classes represented by the sixth-root
condition modulo `49`. -/
theorem signature357_mod49_residues_of_seven_dvd_A {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (h7A : 7 ∣ A) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    B % 49 = 1 ∨ B % 49 = 18 ∨ B % 49 = 19 ∨
      B % 49 = 30 ∨ B % 49 = 31 ∨ B % 49 = 48 := by
  have hSixth :=
    signature357_mod49_sixthRoot_of_seven_dvd_A hAB hAC h7A hEq
  let r := B % 49
  have hr : r < 49 := Nat.mod_lt B (by norm_num)
  have hrSixth : r ^ 6 % 49 = 1 := by
    simpa only [r, ← Nat.pow_mod] using hSixth
  change r = 1 ∨ r = 18 ∨ r = 19 ∨ r = 30 ∨ r = 31 ∨ r = 48
  interval_cases r <;> norm_num at hrSixth
  all_goals norm_num

end BealRegular.Signature357SevenAdic
