import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Conditional discriminant support at `3`, `5`, and `7`

This module records the global number-field consequence of unramifiedness
outside the three exceptional primes in the signature `(3,5,7)` argument.  If
the ring of integers of a number field is unramified at every rational prime
other than `3`, `5`, and `7`, then the absolute discriminant has the form
`3^a * 5^b * 7^c`.  The sign is determined by the parity of the number of
complex places.

The unramifiedness assumption is deliberately stated for the ring of
integers.  A finite-etale integral model of a p-adic scalar extension does not
by itself supply this assumption: one must still compare that model with the
completed maximal order.  The theorems below also give only prime support and
arbitrary nonnegative exponents; they do not establish the sharper exponent
sets in Dahmen--Siksek.  Finally, `NumberField` is a field-valued interface,
so these results do not apply directly to a reducible product algebra.
-/

namespace BealRegular.Signature357DiscriminantSupport

open NumberField

/-- The ring of integers of `K` is unramified at every rational prime other
than `3`, `5`, and `7`.

This is the global maximal-order hypothesis needed to read discriminant
support from `NumberField.not_dvd_discr_iff_isUnramifiedIn`. -/
def IsUnramifiedAwayFrom357 (K : Type*) [Field K] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 3 → p ≠ 5 → p ≠ 7 →
    Algebra.IsUnramifiedIn (NumberField.RingOfIntegers K)
      (Ideal.span {(p : ℤ)})

/-- A nonzero natural number all of whose prime divisors lie in
`{3, 5, 7}` is a product of powers of those three primes. -/
theorem eq_three_pow_mul_five_pow_mul_seven_pow_of_prime_dvd
    {n : ℕ} (hn : n ≠ 0)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ n →
      p = 3 ∨ p = 5 ∨ p = 7) :
    ∃ a b c : ℕ, n = 3 ^ a * 5 ^ b * 7 ^ c := by
  refine ⟨n.factorization 3, n.factorization 5, n.factorization 7, ?_⟩
  calc
    n = n.factorization.prod (fun p e => p ^ e) :=
      (Nat.prod_factorization_pow_eq_self hn).symm
    _ = Finset.prod ({3, 5, 7} : Finset ℕ)
        (fun p => p ^ n.factorization p) := by
      apply Finsupp.prod_of_support_subset
      · intro p hp
        rw [Nat.support_factorization] at hp
        obtain ⟨hprime, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
        simpa only [Finset.mem_insert, Finset.mem_singleton] using
          hsupport p hprime hdvd
      · intro p hp
        simp
    _ = 3 ^ n.factorization 3 * 5 ^ n.factorization 5 *
        7 ^ n.factorization 7 := by
      simp [mul_assoc]

/-- Under unramifiedness away from `3`, `5`, and `7`, every positive prime
dividing the signed number-field discriminant is one of those three primes. -/
theorem prime_eq_three_or_five_or_seven_of_dvd_discr
    (K : Type*) [Field K] [NumberField K]
    (hunramified : IsUnramifiedAwayFrom357 K)
    {p : ℕ} (hp : p.Prime) (hpdiscr : (p : ℤ) ∣ NumberField.discr K) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  rcases eq_or_ne p 3 with h3 | h3
  · exact Or.inl h3
  rcases eq_or_ne p 5 with h5 | h5
  · exact Or.inr (Or.inl h5)
  rcases eq_or_ne p 7 with h7 | h7
  · exact Or.inr (Or.inr h7)
  have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnot : ¬(p : ℤ) ∣ NumberField.discr K :=
    (NumberField.not_dvd_discr_iff_isUnramifiedIn K
      (NumberField.RingOfIntegers K) hpInt).2
      (hunramified p hp h3 h5 h7)
  exact (hnot hpdiscr).elim

/-- Under unramifiedness away from `3`, `5`, and `7`, the absolute
number-field discriminant is a product of arbitrary nonnegative powers of
those three primes. -/
theorem natAbs_discr_eq_three_pow_mul_five_pow_mul_seven_pow
    (K : Type*) [Field K] [NumberField K]
    (hunramified : IsUnramifiedAwayFrom357 K) :
    ∃ a b c : ℕ,
      (NumberField.discr K).natAbs = 3 ^ a * 5 ^ b * 7 ^ c := by
  apply eq_three_pow_mul_five_pow_mul_seven_pow_of_prime_dvd
  · exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K)
  · intro p hp hpdiscr
    apply prime_eq_three_or_five_or_seven_of_dvd_discr K hunramified hp
    exact Int.natAbs_dvd_natAbs.mp (by simpa using hpdiscr)

/-- The signed discriminant equals the supported absolute discriminant times
the sign prescribed by the number of complex places. -/
theorem discr_eq_complexSign_mul_three_pow_mul_five_pow_mul_seven_pow
    (K : Type*) [Field K] [NumberField K]
    (hunramified : IsUnramifiedAwayFrom357 K) :
    ∃ a b c : ℕ,
      NumberField.discr K =
        (-1 : ℤ) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          ((3 ^ a * 5 ^ b * 7 ^ c : ℕ) : ℤ) := by
  obtain ⟨a, b, c, habs⟩ :=
    natAbs_discr_eq_three_pow_mul_five_pow_mul_seven_pow K hunramified
  refine ⟨a, b, c, ?_⟩
  rw [← habs, ← NumberField.sign_discr, Int.sign_mul_natAbs]

/-- If the number of complex places is odd, the supported discriminant is
negative. -/
theorem discr_eq_neg_three_pow_mul_five_pow_mul_seven_pow_of_odd
    (K : Type*) [Field K] [NumberField K]
    (hunramified : IsUnramifiedAwayFrom357 K)
    (hodd : Odd (NumberField.InfinitePlace.nrComplexPlaces K)) :
    ∃ a b c : ℕ,
      NumberField.discr K = -((3 ^ a * 5 ^ b * 7 ^ c : ℕ) : ℤ) := by
  obtain ⟨a, b, c, habc⟩ :=
    discr_eq_complexSign_mul_three_pow_mul_five_pow_mul_seven_pow
      K hunramified
  refine ⟨a, b, c, ?_⟩
  simpa only [hodd.neg_one_pow, neg_mul, one_mul] using habc

/-- In particular, three complex places force the supported discriminant to
be negative. -/
theorem discr_eq_neg_three_pow_mul_five_pow_mul_seven_pow_of_three_complexPlaces
    (K : Type*) [Field K] [NumberField K]
    (hunramified : IsUnramifiedAwayFrom357 K)
    (hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = 3) :
    ∃ a b c : ℕ,
      NumberField.discr K = -((3 ^ a * 5 ^ b * 7 ^ c : ℕ) : ℤ) := by
  apply discr_eq_neg_three_pow_mul_five_pow_mul_seven_pow_of_odd K hunramified
  rw [hcomplex]
  exact ⟨1, by norm_num⟩

end BealRegular.Signature357DiscriminantSupport
