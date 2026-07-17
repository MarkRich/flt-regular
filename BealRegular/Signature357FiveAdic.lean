import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# A five-adic restriction for signature `(3,5,7)`

Suppose natural numbers satisfy

`A ^ 3 + B ^ 5 = C ^ 7`,

both `A` and `B` are coprime to `C`, and `5 ∣ C`.  Reduction modulo `5 ^ 7`
and Euler's theorem force

`A ^ 12500 = 1 (mod 78125)`.

A smaller consequence is `A ^ 4 = 1 (mod 25)`, hence
`A mod 25 ∈ {1, 7, 18, 24}`.  These are conditional necessary restrictions:
the file does not prove `5 ∣ C`, exclude this branch, or prove nonexistence of
`(3,5,7)` solutions.  No positivity or nonzero hypothesis is assumed.
-/

namespace BealRegular.Signature357FiveAdic

private theorem not_five_dvd_right_of_coprime_of_dvd_left
    {x y : ℕ} (hxy : Nat.Coprime x y) (hx : 5 ∣ x) : ¬5 ∣ y := by
  have h5y : Nat.Coprime 5 y := Nat.Coprime.of_dvd_left hx hxy
  exact (by decide : Nat.Prime 5).coprime_iff_not_dvd.mp h5y

private theorem isUnit_zmod78125_of_not_five_dvd {n : ℕ}
    (hn : ¬5 ∣ n) : IsUnit (n : ZMod 78125) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 78125 = 5 ^ 7 by norm_num] using
    (by decide : Nat.Prime 5).coprime_pow_of_not_dvd hn (m := 7)

private theorem mod78125_unit_pow_62500 {a : ZMod 78125}
    (ha : IsUnit a) : a ^ 62500 = 1 := by
  let u : (ZMod 78125)ˣ := ha.unit
  have hu : u ^ Nat.totient 78125 = 1 := ZMod.pow_totient u
  have hv := congrArg (fun x : (ZMod 78125)ˣ ↦ (x : ZMod 78125)) hu
  have htot : Nat.totient 78125 = 62500 := by
    rw [show 78125 = 5 ^ 7 by norm_num]
    rw [Nat.totient_prime_pow (by decide : Nat.Prime 5)
      (by norm_num : 0 < 7)]
    norm_num
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, htot, u,
    IsUnit.unit_spec] using hv

private theorem isUnit_zmod25_of_not_five_dvd {n : ℕ}
    (hn : ¬5 ∣ n) : IsUnit (n : ZMod 25) := by
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show 25 = 5 ^ 2 by norm_num] using
    (by decide : Nat.Prime 5).coprime_pow_of_not_dvd hn (m := 2)

private theorem mod25_unit_pow_20 {a : ZMod 25}
    (ha : IsUnit a) : a ^ 20 = 1 := by
  let u : (ZMod 25)ˣ := ha.unit
  have hu : u ^ Nat.totient 25 = 1 := ZMod.pow_totient u
  have hv := congrArg (fun x : (ZMod 25)ˣ ↦ (x : ZMod 25)) hu
  have htot : Nat.totient 25 = 20 := by
    rw [show 25 = 5 ^ 2 by norm_num]
    rw [Nat.totient_prime_pow (by decide : Nat.Prime 5)
      (by norm_num : 0 < 2)]
    norm_num
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, htot, u,
    IsUnit.unit_spec] using hv

private theorem seventh_cast_eq_zero_mod78125_of_five_dvd {n : ℕ}
    (hn : 5 ∣ n) : (n : ZMod 78125) ^ 7 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  refine ⟨k ^ 7, ?_⟩
  ring

/-- If `A^3 + B^5 = C^7`, both summand bases are coprime to `C`, and
`5 ∣ C`, then `A^12500 = 1 (mod 5^7)`. -/
theorem signature357_mod78125_of_five_dvd_C {A B C : ℕ}
    (hAC : Nat.Coprime A C) (hBC : Nat.Coprime B C)
    (h5C : 5 ∣ C) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    A ^ 12500 % 78125 = 1 := by
  have h5A : ¬5 ∣ A :=
    not_five_dvd_right_of_coprime_of_dvd_left hAC.symm h5C
  have h5B : ¬5 ∣ B :=
    not_five_dvd_right_of_coprime_of_dvd_left hBC.symm h5C
  have hAUnit : IsUnit (A : ZMod 78125) :=
    isUnit_zmod78125_of_not_five_dvd h5A
  have hBUnit : IsUnit (B : ZMod 78125) :=
    isUnit_zmod78125_of_not_five_dvd h5B
  have hEqZ :
      (A : ZMod 78125) ^ 3 + (B : ZMod 78125) ^ 5 =
        (C : ZMod 78125) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ ↦ (n : ZMod 78125)) hEq
  have hZero :
      (A : ZMod 78125) ^ 3 + (B : ZMod 78125) ^ 5 = 0 := by
    rw [seventh_cast_eq_zero_mod78125_of_five_dvd h5C] at hEqZ
    exact hEqZ
  have hUnits : (A : ZMod 78125) ^ 3 = (-(B : ZMod 78125)) ^ 5 := by
    rw [(by decide : Odd 5).neg_pow]
    exact eq_neg_of_add_eq_zero_left hZero
  have hNegBUnit : IsUnit (-(B : ZMod 78125)) := hBUnit.neg
  have hA37500 : (A : ZMod 78125) ^ 37500 = 1 := by
    calc
      (A : ZMod 78125) ^ 37500 = ((A : ZMod 78125) ^ 3) ^ 12500 := by
        simpa using (pow_mul (A : ZMod 78125) 3 12500)
      _ = ((-(B : ZMod 78125)) ^ 5) ^ 12500 := by rw [hUnits]
      _ = (-(B : ZMod 78125)) ^ 62500 := by
        simpa using (pow_mul (-(B : ZMod 78125)) 5 12500).symm
      _ = 1 := mod78125_unit_pow_62500 hNegBUnit
  have hA75000 : (A : ZMod 78125) ^ 75000 = 1 := by
    calc
      (A : ZMod 78125) ^ 75000 =
          ((A : ZMod 78125) ^ 37500) ^ 2 := by
        simpa using (pow_mul (A : ZMod 78125) 37500 2)
      _ = 1 := by rw [hA37500]; norm_num
  have hA62500 : (A : ZMod 78125) ^ 62500 = 1 :=
    mod78125_unit_pow_62500 hAUnit
  have hA12500 : (A : ZMod 78125) ^ 12500 = 1 := by
    have hSplit : (A : ZMod 78125) ^ 75000 =
        (A : ZMod 78125) ^ 62500 * (A : ZMod 78125) ^ 12500 := by
      rw [← pow_add]
    rw [hSplit, hA62500, one_mul] at hA75000
    exact hA75000
  have hCast : ((A ^ 12500 : ℕ) : ZMod 78125) = (1 : ℕ) := by
    simpa only [Nat.cast_pow, Nat.cast_one] using hA12500
  have hMod :=
    (ZMod.natCast_eq_natCast_iff' (A ^ 12500) 1 78125).mp hCast
  simpa using hMod

/-- Under the same hypotheses, the cubic base is a fourth root of unity
modulo `25`. -/
theorem signature357_mod25_fourthRoot_of_five_dvd_C {A B C : ℕ}
    (hAC : Nat.Coprime A C) (hBC : Nat.Coprime B C)
    (h5C : 5 ∣ C) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    A ^ 4 % 25 = 1 := by
  have h5A : ¬5 ∣ A :=
    not_five_dvd_right_of_coprime_of_dvd_left hAC.symm h5C
  have h5B : ¬5 ∣ B :=
    not_five_dvd_right_of_coprime_of_dvd_left hBC.symm h5C
  have hAUnit : IsUnit (A : ZMod 25) :=
    isUnit_zmod25_of_not_five_dvd h5A
  have hBUnit : IsUnit (B : ZMod 25) :=
    isUnit_zmod25_of_not_five_dvd h5B
  have hEqZ :
      (A : ZMod 25) ^ 3 + (B : ZMod 25) ^ 5 =
        (C : ZMod 25) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ ↦ (n : ZMod 25)) hEq
  have hCZero : (C : ZMod 25) ^ 7 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    obtain ⟨k, rfl⟩ := h5C
    refine ⟨5 ^ 5 * k ^ 7, ?_⟩
    ring
  have hZero :
      (A : ZMod 25) ^ 3 + (B : ZMod 25) ^ 5 = 0 := by
    rw [hCZero] at hEqZ
    exact hEqZ
  have hUnits : (A : ZMod 25) ^ 3 = (-(B : ZMod 25)) ^ 5 := by
    rw [(by decide : Odd 5).neg_pow]
    exact eq_neg_of_add_eq_zero_left hZero
  have hNegBUnit : IsUnit (-(B : ZMod 25)) := hBUnit.neg
  have hA12 : (A : ZMod 25) ^ 12 = 1 := by
    calc
      (A : ZMod 25) ^ 12 = ((A : ZMod 25) ^ 3) ^ 4 := by
        simpa using (pow_mul (A : ZMod 25) 3 4)
      _ = ((-(B : ZMod 25)) ^ 5) ^ 4 := by rw [hUnits]
      _ = (-(B : ZMod 25)) ^ 20 := by
        simpa using (pow_mul (-(B : ZMod 25)) 5 4).symm
      _ = 1 := mod25_unit_pow_20 hNegBUnit
  have hA20 : (A : ZMod 25) ^ 20 = 1 := mod25_unit_pow_20 hAUnit
  have hA8 : (A : ZMod 25) ^ 8 = 1 := by
    have hSplit : (A : ZMod 25) ^ 20 =
        (A : ZMod 25) ^ 12 * (A : ZMod 25) ^ 8 := by
      rw [← pow_add]
    rw [hSplit, hA12, one_mul] at hA20
    exact hA20
  have hA4 : (A : ZMod 25) ^ 4 = 1 := by
    have hSplit : (A : ZMod 25) ^ 12 =
        (A : ZMod 25) ^ 8 * (A : ZMod 25) ^ 4 := by
      rw [← pow_add]
    rw [hSplit, hA8, one_mul] at hA12
    exact hA12
  have hCast : ((A ^ 4 : ℕ) : ZMod 25) = (1 : ℕ) := by
    simpa only [Nat.cast_pow, Nat.cast_one] using hA4
  have hMod := (ZMod.natCast_eq_natCast_iff' (A ^ 4) 1 25).mp hCast
  simpa using hMod

/-- The preceding fourth-root condition leaves exactly four residue classes
for `A` modulo `25`. -/
theorem signature357_mod25_residues_of_five_dvd_C {A B C : ℕ}
    (hAC : Nat.Coprime A C) (hBC : Nat.Coprime B C)
    (h5C : 5 ∣ C) (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    A % 25 = 1 ∨ A % 25 = 7 ∨ A % 25 = 18 ∨ A % 25 = 24 := by
  have hFourth :=
    signature357_mod25_fourthRoot_of_five_dvd_C hAC hBC h5C hEq
  let r := A % 25
  have hr : r < 25 := Nat.mod_lt A (by norm_num)
  have hrFourth : r ^ 4 % 25 = 1 := by
    simpa only [r, ← Nat.pow_mod] using hFourth
  change r = 1 ∨ r = 7 ∨ r = 18 ∨ r = 24
  interval_cases r <;> norm_num at hrFourth
  all_goals norm_num

end BealRegular.Signature357FiveAdic
