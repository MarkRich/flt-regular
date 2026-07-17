import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Prime-power restrictions for the `(3,5,7)` signature

For a pairwise-coprime natural solution of

`A ^ 3 + B ^ 5 = C ^ 7`,

this file records the strongest congruence obtained in each branch merely by
making the powered even term vanish:

* `Even A` gives `B = C (mod 8)`;
* `Even B` gives `C = A ^ 5 (mod 32)`;
* `Even C` gives `B = -A ^ 7 (mod 128)`.

No positivity or nonzero hypothesis is used.  The conclusions are branch
implications: they neither assert that a specified base is even nor exclude
any branch, and they do not solve the `(3,5,7)` signature.
-/

namespace BealRegular.Signature357PrimePower

/-! ## Kernel-reduced unit calculations -/

private theorem mod8_fifth_eq_seventh_units :
    ∀ b c : ZMod 8,
      IsUnit b → IsUnit c → b ^ 5 = c ^ 7 → b = c := by
  decide

private theorem mod32_cubic_eq_seventh_units :
    ∀ a c : ZMod 32,
      IsUnit a → IsUnit c → a ^ 3 = c ^ 7 → c = a ^ 5 := by
  decide

set_option maxRecDepth 100000 in
private theorem mod128_cubic_plus_fifth_units :
    ∀ a b : ZMod 128,
      IsUnit a → IsUnit b → a ^ 3 + b ^ 5 = 0 → b + a ^ 7 = 0 := by
  decide

/-! ## Elementary parity and transport helpers -/

/-- If the left member of a coprime pair is even, the right member is odd. -/
private theorem not_even_right_of_coprime_of_even_left {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : Even m) : ¬Even n := by
  intro hn
  have hTwo : (2 : ℕ) = 1 :=
    Nat.eq_one_of_dvd_coprimes hmn
      (even_iff_two_dvd.mp hm) (even_iff_two_dvd.mp hn)
  exact (by decide : (2 : ℕ) ≠ 1) hTwo

private theorem isUnit_zmod8_of_not_even {n : ℕ} (hn : ¬Even n) :
    IsUnit (n : ZMod 8) := by
  rw [ZMod.isUnit_iff_coprime]
  have h2 : ¬2 ∣ n := by simpa only [even_iff_two_dvd] using hn
  simpa only [show 8 = 2 ^ 3 by decide] using
    Nat.prime_two.coprime_pow_of_not_dvd h2 (m := 3)

private theorem isUnit_zmod32_of_not_even {n : ℕ} (hn : ¬Even n) :
    IsUnit (n : ZMod 32) := by
  rw [ZMod.isUnit_iff_coprime]
  have h2 : ¬2 ∣ n := by simpa only [even_iff_two_dvd] using hn
  simpa only [show 32 = 2 ^ 5 by decide] using
    Nat.prime_two.coprime_pow_of_not_dvd h2 (m := 5)

private theorem isUnit_zmod128_of_not_even {n : ℕ} (hn : ¬Even n) :
    IsUnit (n : ZMod 128) := by
  rw [ZMod.isUnit_iff_coprime]
  have h2 : ¬2 ∣ n := by simpa only [even_iff_two_dvd] using hn
  simpa only [show 128 = 2 ^ 7 by decide] using
    Nat.prime_two.coprime_pow_of_not_dvd h2 (m := 7)

private theorem cube_cast_eq_zero_mod8_of_even {n : ℕ} (hn : Even n) :
    (n : ZMod 8) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  refine ⟨k ^ 3, ?_⟩
  ring

private theorem fifth_cast_eq_zero_mod32_of_even {n : ℕ} (hn : Even n) :
    (n : ZMod 32) ^ 5 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  refine ⟨k ^ 5, ?_⟩
  ring

private theorem seventh_cast_eq_zero_mod128_of_even {n : ℕ} (hn : Even n) :
    (n : ZMod 128) ^ 7 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨k, rfl⟩ := hn
  refine ⟨k ^ 7, ?_⟩
  ring

/-! ## Natural-number branch restrictions -/

/-- The maximal vanishing-term 2-adic table for a pairwise-coprime
`(3,5,7)` equation.

Each implication uses pairwise coprimality only to show that the other two
bases are odd once its named base is even.  No positivity assumption is
needed, and an implication is vacuous when its named base is odd.
-/
theorem signature357_two_adic_branch_table {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (hBC : Nat.Coprime B C)
    (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    (Even A → B % 8 = C % 8) ∧
    (Even B → C % 32 = A ^ 5 % 32) ∧
    (Even C → (B + A ^ 7) % 128 = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hA
    have hB : ¬Even B :=
      not_even_right_of_coprime_of_even_left hAB hA
    have hC : ¬Even C :=
      not_even_right_of_coprime_of_even_left hAC hA
    have hEqZ :
        (A : ZMod 8) ^ 3 + (B : ZMod 8) ^ 5 = (C : ZMod 8) ^ 7 := by
      simpa only [Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ ↦ (n : ZMod 8)) hEq
    have hBCZ : (B : ZMod 8) ^ 5 = (C : ZMod 8) ^ 7 := by
      rw [cube_cast_eq_zero_mod8_of_even hA, zero_add] at hEqZ
      exact hEqZ
    have hZ : (B : ZMod 8) = (C : ZMod 8) :=
      mod8_fifth_eq_seventh_units _ _
        (isUnit_zmod8_of_not_even hB) (isUnit_zmod8_of_not_even hC) hBCZ
    exact (ZMod.natCast_eq_natCast_iff' B C 8).mp hZ
  · intro hB
    have hA : ¬Even A :=
      not_even_right_of_coprime_of_even_left hAB.symm hB
    have hC : ¬Even C :=
      not_even_right_of_coprime_of_even_left hBC hB
    have hEqZ :
        (A : ZMod 32) ^ 3 + (B : ZMod 32) ^ 5 = (C : ZMod 32) ^ 7 := by
      simpa only [Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ ↦ (n : ZMod 32)) hEq
    have hACZ : (A : ZMod 32) ^ 3 = (C : ZMod 32) ^ 7 := by
      rw [fifth_cast_eq_zero_mod32_of_even hB, add_zero] at hEqZ
      exact hEqZ
    have hZ : (C : ZMod 32) = (A : ZMod 32) ^ 5 :=
      mod32_cubic_eq_seventh_units _ _
        (isUnit_zmod32_of_not_even hA) (isUnit_zmod32_of_not_even hC) hACZ
    have hZ' : (C : ZMod 32) = (A ^ 5 : ℕ) := by
      simpa only [Nat.cast_pow] using hZ
    exact (ZMod.natCast_eq_natCast_iff' C (A ^ 5) 32).mp hZ'
  · intro hC
    have hA : ¬Even A :=
      not_even_right_of_coprime_of_even_left hAC.symm hC
    have hB : ¬Even B :=
      not_even_right_of_coprime_of_even_left hBC.symm hC
    have hEqZ :
        (A : ZMod 128) ^ 3 + (B : ZMod 128) ^ 5 =
          (C : ZMod 128) ^ 7 := by
      simpa only [Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ ↦ (n : ZMod 128)) hEq
    have hABZ : (A : ZMod 128) ^ 3 + (B : ZMod 128) ^ 5 = 0 := by
      rw [seventh_cast_eq_zero_mod128_of_even hC] at hEqZ
      exact hEqZ
    have hZ : (B : ZMod 128) + (A : ZMod 128) ^ 7 = 0 :=
      mod128_cubic_plus_fifth_units _ _
        (isUnit_zmod128_of_not_even hA) (isUnit_zmod128_of_not_even hB) hABZ
    have hZ' : (B + A ^ 7 : ℕ) = (0 : ZMod 128) := by
      simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_zero] using hZ
    exact Nat.dvd_iff_mod_eq_zero.mp
      ((ZMod.natCast_eq_zero_iff (B + A ^ 7) 128).mp hZ')

/-- Convenience form of the modulus-`128` conclusion in the `C`-even
branch. -/
theorem signature357_mod128_of_even_C {A B C : ℕ}
    (hAB : Nat.Coprime A B) (hAC : Nat.Coprime A C)
    (hBC : Nat.Coprime B C) (hC : Even C)
    (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    (B + A ^ 7) % 128 = 0 :=
  (signature357_two_adic_branch_table hAB hAC hBC hEq).2.2 hC

end BealRegular.Signature357PrimePower
