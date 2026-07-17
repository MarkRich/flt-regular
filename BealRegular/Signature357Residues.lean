import Mathlib.Data.ZMod.Basic

/-!
# Local restrictions for the `(3,5,7)` signature

This module records three unconditional local obstructions for

`A ^ 3 + B ^ 5 = C ^ 7`.

The finite residue checks use ordinary kernel reduction. The public theorems
then expose the exclusions over `ZMod` and over natural numbers. No positivity
or coprimality hypothesis is needed.
-/

namespace BealRegular.Signature357Residues

/-! ## Kernel-checked finite residue facts -/

private theorem mod31_forbidden_rhs :
    ∀ a b : ZMod 31,
      a ^ 3 + b ^ 5 ≠ (14 : ZMod 31) ^ 7 ∧
      a ^ 3 + b ^ 5 ≠ (17 : ZMod 31) ^ 7 := by
  decide

private theorem mod43_forbidden_fifth_power_terms :
    ∀ a c : ZMod 43,
      a ^ 3 + (18 : ZMod 43) ^ 5 ≠ c ^ 7 ∧
      a ^ 3 + (19 : ZMod 43) ^ 5 ≠ c ^ 7 ∧
      a ^ 3 + (24 : ZMod 43) ^ 5 ≠ c ^ 7 ∧
      a ^ 3 + (25 : ZMod 43) ^ 5 ≠ c ^ 7 := by
  decide

set_option maxRecDepth 100000 in
private theorem mod71_forbidden_cubic_terms :
    ∀ b c : ZMod 71,
      (2 : ZMod 71) ^ 3 + b ^ 5 ≠ c ^ 7 ∧
      (18 : ZMod 71) ^ 3 + b ^ 5 ≠ c ^ 7 ∧
      (33 : ZMod 71) ^ 3 + b ^ 5 ≠ c ^ 7 ∧
      (38 : ZMod 71) ^ 3 + b ^ 5 ≠ c ^ 7 ∧
      (53 : ZMod 71) ^ 3 + b ^ 5 ≠ c ^ 7 ∧
      (69 : ZMod 71) ^ 3 + b ^ 5 ≠ c ^ 7 := by
  decide

/-! ## Reusable `ZMod` statements -/

/-- A solution modulo `31` cannot have its seventh-power base congruent to
`14` or `17` (the two residues are negatives of one another). -/
theorem signature357_mod31_C_exclusion {a b c : ZMod 31}
    (hEq : a ^ 3 + b ^ 5 = c ^ 7) :
    c ≠ 14 ∧ c ≠ 17 := by
  constructor
  · intro hc
    subst c
    exact (mod31_forbidden_rhs a b).1 hEq
  · intro hc
    subst c
    exact (mod31_forbidden_rhs a b).2 hEq

/-- A solution modulo `43` cannot have its fifth-power base in the four
residue classes `±18, ±19`. -/
theorem signature357_mod43_B_exclusion {a b c : ZMod 43}
    (hEq : a ^ 3 + b ^ 5 = c ^ 7) :
    b ≠ 18 ∧ b ≠ 19 ∧ b ≠ 24 ∧ b ≠ 25 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hb
    subst b
    exact (mod43_forbidden_fifth_power_terms a c).1 hEq
  · intro hb
    subst b
    exact (mod43_forbidden_fifth_power_terms a c).2.1 hEq
  · intro hb
    subst b
    exact (mod43_forbidden_fifth_power_terms a c).2.2.1 hEq
  · intro hb
    subst b
    exact (mod43_forbidden_fifth_power_terms a c).2.2.2 hEq

/-- A solution modulo `71` cannot have its cubic-power base in the six
residue classes `±2, ±18, ±33`. -/
theorem signature357_mod71_A_exclusion {a b c : ZMod 71}
    (hEq : a ^ 3 + b ^ 5 = c ^ 7) :
    a ≠ 2 ∧ a ≠ 18 ∧ a ≠ 33 ∧ a ≠ 38 ∧ a ≠ 53 ∧ a ≠ 69 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ha
    subst a
    exact (mod71_forbidden_cubic_terms b c).1 hEq
  · intro ha
    subst a
    exact (mod71_forbidden_cubic_terms b c).2.1 hEq
  · intro ha
    subst a
    exact (mod71_forbidden_cubic_terms b c).2.2.1 hEq
  · intro ha
    subst a
    exact (mod71_forbidden_cubic_terms b c).2.2.2.1 hEq
  · intro ha
    subst a
    exact (mod71_forbidden_cubic_terms b c).2.2.2.2.1 hEq
  · intro ha
    subst a
    exact (mod71_forbidden_cubic_terms b c).2.2.2.2.2 hEq

/-! ## Natural-number consequences -/

/-- Natural-number form of the modulo-`31` seventh-power-base exclusion. -/
theorem signature357_nat_mod31_C_exclusion {A B C : ℕ}
    (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    C % 31 ≠ 14 ∧ C % 31 ≠ 17 := by
  have hEqZ :
      (A : ZMod 31) ^ 3 + (B : ZMod 31) ^ 5 = (C : ZMod 31) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ZMod 31)) hEq
  obtain ⟨h14, h17⟩ := signature357_mod31_C_exclusion hEqZ
  constructor
  · intro hC
    apply h14
    exact (ZMod.natCast_eq_natCast_iff' C 14 31).2 (by simpa using hC)
  · intro hC
    apply h17
    exact (ZMod.natCast_eq_natCast_iff' C 17 31).2 (by simpa using hC)

/-- Natural-number form of the modulo-`43` fifth-power-base exclusion. -/
theorem signature357_nat_mod43_B_exclusion {A B C : ℕ}
    (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    B % 43 ≠ 18 ∧ B % 43 ≠ 19 ∧ B % 43 ≠ 24 ∧ B % 43 ≠ 25 := by
  have hEqZ :
      (A : ZMod 43) ^ 3 + (B : ZMod 43) ^ 5 = (C : ZMod 43) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ZMod 43)) hEq
  obtain ⟨h18, h19, h24, h25⟩ := signature357_mod43_B_exclusion hEqZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hB
    apply h18
    exact (ZMod.natCast_eq_natCast_iff' B 18 43).2 (by simpa using hB)
  · intro hB
    apply h19
    exact (ZMod.natCast_eq_natCast_iff' B 19 43).2 (by simpa using hB)
  · intro hB
    apply h24
    exact (ZMod.natCast_eq_natCast_iff' B 24 43).2 (by simpa using hB)
  · intro hB
    apply h25
    exact (ZMod.natCast_eq_natCast_iff' B 25 43).2 (by simpa using hB)

/-- Natural-number form of the modulo-`71` cubic-power-base exclusion. -/
theorem signature357_nat_mod71_A_exclusion {A B C : ℕ}
    (hEq : A ^ 3 + B ^ 5 = C ^ 7) :
    A % 71 ≠ 2 ∧ A % 71 ≠ 18 ∧ A % 71 ≠ 33 ∧
      A % 71 ≠ 38 ∧ A % 71 ≠ 53 ∧ A % 71 ≠ 69 := by
  have hEqZ :
      (A : ZMod 71) ^ 3 + (B : ZMod 71) ^ 5 = (C : ZMod 71) ^ 7 := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ZMod 71)) hEq
  obtain ⟨h2, h18, h33, h38, h53, h69⟩ := signature357_mod71_A_exclusion hEqZ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hA
    apply h2
    exact (ZMod.natCast_eq_natCast_iff' A 2 71).2 (by simpa using hA)
  · intro hA
    apply h18
    exact (ZMod.natCast_eq_natCast_iff' A 18 71).2 (by simpa using hA)
  · intro hA
    apply h33
    exact (ZMod.natCast_eq_natCast_iff' A 33 71).2 (by simpa using hA)
  · intro hA
    apply h38
    exact (ZMod.natCast_eq_natCast_iff' A 38 71).2 (by simpa using hA)
  · intro hA
    apply h53
    exact (ZMod.natCast_eq_natCast_iff' A 53 71).2 (by simpa using hA)
  · intro hA
    apply h69
    exact (ZMod.natCast_eq_natCast_iff' A 69 71).2 (by simpa using hA)

end BealRegular.Signature357Residues
