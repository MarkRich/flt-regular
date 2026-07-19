import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Adic completeness for powers of an ideal

This module proves that replacing an ideal of definition by any positive
power preserves adic completeness.  The two adic filtrations are cofinal:
the `n`th power of `I ^ N` is the `(N * n)`th power of `I`.  Reindexing by
this cofinal subsequence preserves both Hausdorffness and convergence of
Cauchy sequences.

For the signature `(3,5,7)` program, this permits coprime factor lifting at
the higher-precision ideal `(p) ^ (k * r)`.  The result itself is generic; it
does not construct a polynomial factorization, rescale a lifted factor,
classify ramification, exclude signature `(3,5,7)`, or prove Beal's
conjecture.
-/

namespace BealRegular.AdicCompletenessPowers

universe u v

/-- A module complete for `I` is complete for every positive power `I ^ N`.
Equivalently, passage to the cofinal subsequence of indices `N * n` preserves
adic completeness. -/
theorem isAdicComplete_pow_of_pos
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) [IsAdicComplete I M]
    (N : ℕ) (hN : 0 < N) :
    IsAdicComplete (I ^ N) M where
  toIsHausdorff := ⟨fun x hx ↦
    IsHausdorff.haus (I := I) inferInstance x fun n ↦ by
      apply SModEq.mono _ (hx n)
      simpa only [← pow_mul] using
        ((Submodule.smul_mono_left
          (Ideal.pow_le_pow_right (I := I) (Nat.le_mul_of_pos_left n hN))) :
            I ^ (N * n) • (⊤ : Submodule R M) ≤ I ^ n • ⊤)⟩
  toIsPrecomplete := ⟨fun f hf ↦ by
    have hfI : ∀ {m n}, m ≤ n →
        f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)] := by
      intro m n hmn
      apply SModEq.mono _ (hf hmn)
      simpa only [← pow_mul] using
        ((Submodule.smul_mono_left
          (Ideal.pow_le_pow_right (I := I) (Nat.le_mul_of_pos_left m hN))) :
            I ^ (N * m) • (⊤ : Submodule R M) ≤ I ^ m • ⊤)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance hfI
    refine ⟨L, fun n ↦ ?_⟩
    trans f (N * n)
    · exact hf (Nat.le_mul_of_pos_left n hN)
    · simpa only [← pow_mul] using hL (N * n)⟩

end BealRegular.AdicCompletenessPowers
