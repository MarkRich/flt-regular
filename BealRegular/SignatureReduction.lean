import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.GCD.Basic

/-!
# Coordinatewise reduction of Beal signatures

Every exponent greater than two has either a factor `4` or an odd prime
factor.  Applying that elementary dichotomy independently to the three
coordinates of a Beal equation reduces an arbitrary signature `(x, y, z)` to
one whose entries are each either `4` or an odd prime.

The common-factor predicate below deliberately asks for one prime dividing all
three bases.  This is Beal's condition; it is strictly weaker than pairwise
coprimality.
-/

@[expose] public section

namespace BealRegular.SignatureReduction

/-- A normalized Beal exponent is either `4` or an odd prime. -/
def IsReducedBealExponent (n : ℕ) : Prop :=
  n = 4 ∨ (n.Prime ∧ Odd n)

/-- Beal's common-factor condition: one prime divides all three bases. -/
def HasCommonPrimeFactor (A B C : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ∣ A ∧ p ∣ B ∧ p ∣ C

/-- Every normalized exponent is greater than two. -/
theorem IsReducedBealExponent.two_lt {n : ℕ} (hn : IsReducedBealExponent n) :
    2 < n := by
  rcases hn with rfl | ⟨hnPrime, ⟨k, hk⟩⟩
  · omega
  · have hnTwoLe := hnPrime.two_le
    omega

/-- Beal's conjecture over nonzero natural-number bases. -/
def BealConjecture : Prop :=
  ∀ {A B C x y z : ℕ},
    2 < x → 2 < y → 2 < z →
    A ≠ 0 → B ≠ 0 → C ≠ 0 →
    A ^ x + B ^ y = C ^ z →
    HasCommonPrimeFactor A B C

/-- Beal's conjecture restricted coordinatewise to exponent `4` or an odd
prime. -/
def ReducedBealConjecture : Prop :=
  ∀ {A B C p q r : ℕ},
    IsReducedBealExponent p →
    IsReducedBealExponent q →
    IsReducedBealExponent r →
    A ≠ 0 → B ≠ 0 → C ≠ 0 →
    A ^ p + B ^ q = C ^ r →
    HasCommonPrimeFactor A B C

/-- Every exponent greater than two is a positive multiple of `4` or of an
odd prime. -/
theorem exists_reduced_exponent_factorization {n : ℕ} (hn : 2 < n) :
    ∃ e k : ℕ, IsReducedBealExponent e ∧ 0 < k ∧ n = k * e := by
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn with hfour |
    ⟨p, hp, hpn, hodd⟩
  · obtain ⟨k, hk⟩ := hfour
    refine ⟨4, k, Or.inl rfl, ?_, ?_⟩
    · apply Nat.pos_of_ne_zero
      intro hk0
      subst k
      simp at hk
      omega
    · simpa [Nat.mul_comm] using hk
  · obtain ⟨k, hk⟩ := hpn
    refine ⟨p, k, Or.inr ⟨hp, hodd⟩, ?_, ?_⟩
    · apply Nat.pos_of_ne_zero
      intro hk0
      subst k
      simp at hk
      omega
    · simpa [Nat.mul_comm] using hk

/-- Raising each base to a positive power preserves exactly the set of primes
common to all three bases. -/
theorem hasCommonPrimeFactor_powers_iff {A B C k l m : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hm : 0 < m) :
    HasCommonPrimeFactor (A ^ k) (B ^ l) (C ^ m) ↔
      HasCommonPrimeFactor A B C := by
  constructor
  · rintro ⟨p, hp, hpA, hpB, hpC⟩
    exact ⟨p, hp, hp.dvd_of_dvd_pow hpA, hp.dvd_of_dvd_pow hpB,
      hp.dvd_of_dvd_pow hpC⟩
  · rintro ⟨p, hp, hpA, hpB, hpC⟩
    exact ⟨p, hp, dvd_pow hpA hk.ne', dvd_pow hpB hl.ne', dvd_pow hpC hm.ne'⟩

/-- The triple-common-prime condition is equivalent to the triple gcd being
different from one.  In particular, this is not pairwise coprimality. -/
theorem hasCommonPrimeFactor_iff_gcd_ne_one {A B C : ℕ} :
    HasCommonPrimeFactor A B C ↔ Nat.gcd (Nat.gcd A B) C ≠ 1 := by
  constructor
  · rintro ⟨p, hp, hpA, hpB, hpC⟩ hgcd
    have hpGcd : p ∣ Nat.gcd (Nat.gcd A B) C :=
      Nat.dvd_gcd (Nat.dvd_gcd hpA hpB) hpC
    rw [hgcd] at hpGcd
    exact hp.not_dvd_one hpGcd
  · intro hgcd
    obtain ⟨p, hp, hpGcd⟩ := Nat.exists_prime_and_dvd hgcd
    refine ⟨p, hp, ?_, ?_, ?_⟩
    · exact hpGcd.trans ((Nat.gcd_dvd_left (Nat.gcd A B) C).trans
        (Nat.gcd_dvd_left A B))
    · exact hpGcd.trans ((Nat.gcd_dvd_left (Nat.gcd A B) C).trans
        (Nat.gcd_dvd_right A B))
    · exact hpGcd.trans (Nat.gcd_dvd_right (Nat.gcd A B) C)

/-- Equivalently, positive coordinatewise powers preserve the assertion that
the triple gcd is one. -/
theorem gcd_powers_eq_one_iff {A B C k l m : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hm : 0 < m) :
    Nat.gcd (Nat.gcd (A ^ k) (B ^ l)) (C ^ m) = 1 ↔
      Nat.gcd (Nat.gcd A B) C = 1 := by
  constructor
  · intro hpowers
    by_contra horiginal
    have hcommon : HasCommonPrimeFactor A B C :=
      hasCommonPrimeFactor_iff_gcd_ne_one.mpr horiginal
    have hcommonPowers := (hasCommonPrimeFactor_powers_iff hk hl hm).mpr hcommon
    exact (hasCommonPrimeFactor_iff_gcd_ne_one.mp hcommonPowers) hpowers
  · intro horiginal
    by_contra hpowers
    have hcommonPowers : HasCommonPrimeFactor (A ^ k) (B ^ l) (C ^ m) :=
      hasCommonPrimeFactor_iff_gcd_ne_one.mpr hpowers
    have hcommon := (hasCommonPrimeFactor_powers_iff hk hl hm).mp hcommonPowers
    exact (hasCommonPrimeFactor_iff_gcd_ne_one.mp hcommon) horiginal

/-- Any nonzero solution of a Beal-type equation reduces coordinatewise to a
nonzero solution whose three exponents are each `4` or an odd prime.  The
triple-common-prime condition is preserved exactly. -/
theorem exists_reduced_generalized_fermat
    {A B C x y z : ℕ}
    (hx : 2 < x) (hy : 2 < y) (hz : 2 < z)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hEq : A ^ x + B ^ y = C ^ z) :
    ∃ p q r k l m : ℕ,
      IsReducedBealExponent p ∧
      IsReducedBealExponent q ∧
      IsReducedBealExponent r ∧
      0 < k ∧ 0 < l ∧ 0 < m ∧
      x = k * p ∧ y = l * q ∧ z = m * r ∧
      A ^ k ≠ 0 ∧ B ^ l ≠ 0 ∧ C ^ m ≠ 0 ∧
      (A ^ k) ^ p + (B ^ l) ^ q = (C ^ m) ^ r ∧
      (HasCommonPrimeFactor (A ^ k) (B ^ l) (C ^ m) ↔
        HasCommonPrimeFactor A B C) := by
  obtain ⟨p, k, hp, hk, hxp⟩ := exists_reduced_exponent_factorization hx
  obtain ⟨q, l, hq, hl, hyq⟩ := exists_reduced_exponent_factorization hy
  obtain ⟨r, m, hr, hm, hzr⟩ := exists_reduced_exponent_factorization hz
  refine ⟨p, q, r, k, l, m, hp, hq, hr, hk, hl, hm, hxp, hyq, hzr,
    pow_ne_zero k hA, pow_ne_zero l hB, pow_ne_zero m hC, ?_,
    hasCommonPrimeFactor_powers_iff hk hl hm⟩
  simpa only [← pow_mul, ← hxp, ← hyq, ← hzr] using hEq

/-- Beal's conjecture is equivalent to its coordinatewise reduced family:
each exponent is either `4` or an odd prime. -/
theorem bealConjecture_iff_reducedBealConjecture :
    BealConjecture ↔ ReducedBealConjecture := by
  constructor
  · intro hBeal A B C p q r hp hq hr hA hB hC hEq
    exact hBeal hp.two_lt hq.two_lt hr.two_lt hA hB hC hEq
  · intro hReduced A B C x y z hx hy hz hA hB hC hEq
    obtain ⟨p, q, r, k, l, m, hp, hq, hr, hk, hl, hm, _hxp, _hyq, _hzr,
      hAk, hBl, hCm, hReducedEq, hCommon⟩ :=
      exists_reduced_generalized_fermat hx hy hz hA hB hC hEq
    exact hCommon.mp (hReduced hp hq hr hAk hBl hCm hReducedEq)

end BealRegular.SignatureReduction
