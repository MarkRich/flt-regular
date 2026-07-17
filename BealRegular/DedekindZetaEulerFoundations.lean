module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Foundations for the Dedekind-zeta Euler product

This file supplies two generic ingredients for the downstream Euler-product proof.
First, unique factorization of nonzero ideals in a Dedekind domain is packaged
as an equivalence with finite multisets of height-one prime ideals, including
the corresponding norm-product and fixed-norm coefficient identities. Second,
the ideal-count Dirichlet series defining a number field's Dedekind zeta
function is shown to be absolutely summable, and to sum to `dedekindZeta`, on
the half-plane `Re(s) > 1`.

This file itself does not construct the infinite Euler product.  That grouping
is proved in `MultisetEulerProduct` and specialized to number fields in
`DedekindZetaEulerProduct`.  No cyclotomic factorization into Dirichlet
`L`-functions or analytic-continuation argument is claimed here.
-/

@[expose] public section

open Filter Ideal NumberField Topology Asymptotics
open scoped NumberField nonZeroDivisors

namespace BealRegular.DedekindZetaEulerFoundations

noncomputable section

open UniqueFactorizationMonoid
open IsDedekindDomain

section IdealFactorization

variable (R : Type*) [CommRing R] [IsDedekindDomain R]

/-- The multiset of height-one prime ideals in the unique factorization of a
nonzero ideal of a Dedekind domain. -/
def primeFactors (I : (Ideal R)⁰) : Multiset (HeightOneSpectrum R) :=
  (normalizedFactors (I : Ideal R)).pmap
    (fun _ hP ↦ HeightOneSpectrum.ofPrime hP)
    (fun P hP ↦ prime_of_normalized_factor P hP)

/-- Forgetting the primality witnesses in `primeFactors` recovers Mathlib's
normalized ideal factorization exactly. -/
theorem map_asIdeal_primeFactors (I : (Ideal R)⁰) :
    (primeFactors R I).map HeightOneSpectrum.asIdeal =
      normalizedFactors (I : Ideal R) := by
  classical
  rw [primeFactors, Multiset.map_pmap]
  simpa [HeightOneSpectrum.ofPrime] using
    (Multiset.pmap_eq_map (fun P : Ideal R ↦ Prime P) id
      (normalizedFactors (I : Ideal R))
      (fun P hP ↦ prime_of_normalized_factor P hP))

/-- Multiply a finite multiset of height-one prime ideals. The resulting
ideal is nonzero. -/
def ofPrimeFactors (m : Multiset (HeightOneSpectrum R)) : (Ideal R)⁰ :=
  ⟨(m.map HeightOneSpectrum.asIdeal).prod,
    mem_nonZeroDivisors_of_ne_zero (by
      apply Multiset.prod_ne_zero
      simp only [Multiset.mem_map, not_exists, not_and]
      intro v _
      exact v.ne_bot)⟩

theorem ofPrimeFactors_primeFactors (I : (Ideal R)⁰) :
    ofPrimeFactors R (primeFactors R I) = I := by
  apply Subtype.ext
  change ((primeFactors R I).map HeightOneSpectrum.asIdeal).prod = (I : Ideal R)
  rw [map_asIdeal_primeFactors,
    Ideal.prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero I)]

theorem primeFactors_ofPrimeFactors (m : Multiset (HeightOneSpectrum R)) :
    primeFactors R (ofPrimeFactors R m) = m := by
  apply Multiset.map_injective HeightOneSpectrum.asIdeal_injective
  rw [map_asIdeal_primeFactors]
  apply normalizedFactors_prod_of_prime
  intro P hP
  rw [Multiset.mem_map] at hP
  obtain ⟨v, _, rfl⟩ := hP
  exact v.prime

/-- Unique factorization identifies nonzero ideals of a Dedekind domain with
finite multisets of its height-one prime ideals. -/
def primeFactorsEquiv : (Ideal R)⁰ ≃ Multiset (HeightOneSpectrum R) where
  toFun := primeFactors R
  invFun := ofPrimeFactors R
  left_inv := ofPrimeFactors_primeFactors R
  right_inv := primeFactors_ofPrimeFactors R

variable [Module.Free ℤ R]

/-- Under the prime-factor multiset equivalence, ideal norm is the product of
the norms of the prime factors. -/
theorem absNorm_ofPrimeFactors (m : Multiset (HeightOneSpectrum R)) :
    absNorm ((ofPrimeFactors R m : (Ideal R)⁰) : Ideal R) =
      (m.map (fun v ↦ absNorm v.asIdeal)).prod := by
  change absNorm ((m.map HeightOneSpectrum.asIdeal).prod) = _
  rw [map_multiset_prod]
  simp only [Multiset.map_map, Function.comp_apply]

/-- Norm factorization for an arbitrary nonzero ideal, stated directly using
its unique multiset of height-one prime factors. -/
theorem absNorm_eq_primeFactors_prod (I : (Ideal R)⁰) :
    absNorm (I : Ideal R) =
      ((primeFactors R I).map (fun v ↦ absNorm v.asIdeal)).prod := by
  rw [← absNorm_ofPrimeFactors R (primeFactors R I), ofPrimeFactors_primeFactors]

variable [Module.Finite ℤ R]

/-- For a positive target norm, passing between all ideals and nonzero ideals
does not change the norm fiber. -/
def idealsOfNormEquivNonzeroIdealsOfNorm {n : ℕ} (hn : n ≠ 0) :
    {I : Ideal R // absNorm I = n} ≃
      {I : (Ideal R)⁰ // absNorm (I : Ideal R) = n} where
  toFun I :=
    ⟨⟨I, mem_nonZeroDivisors_of_ne_zero (by
      intro hI
      apply hn
      rw [← I.property]
      exact Ideal.absNorm_eq_zero_iff.mpr hI)⟩, I.property⟩
  invFun I := ⟨(I.1 : Ideal R), I.property⟩
  left_inv I := by ext; rfl
  right_inv I := by ext; rfl

/-- Ideals of a fixed positive norm are equivalent to finite multisets of
height-one prime ideals whose norms have the prescribed product. -/
def idealsOfNormEquivPrimeFactorMultisets {n : ℕ} (hn : n ≠ 0) :
    {I : Ideal R // absNorm I = n} ≃
      {m : Multiset (HeightOneSpectrum R) //
        (m.map (fun v ↦ absNorm v.asIdeal)).prod = n} :=
  (idealsOfNormEquivNonzeroIdealsOfNorm R hn).trans <|
    (primeFactorsEquiv R).subtypeEquiv fun I ↦ by
      rw [absNorm_eq_primeFactors_prod]
      rfl

/-- For every nonzero `n`, the Dedekind-zeta coefficient counts prime-ideal
factor multisets whose norm product is `n`. -/
theorem card_idealsOfNorm_eq_card_primeFactorMultisets {n : ℕ} (hn : n ≠ 0) :
    Nat.card {I : Ideal R // absNorm I = n} =
      Nat.card {m : Multiset (HeightOneSpectrum R) //
        (m.map (fun v ↦ absNorm v.asIdeal)).prod = n} :=
  Nat.card_congr (idealsOfNormEquivPrimeFactorMultisets R hn)

end IdealFactorization

section Convergence

/-- The Dirichlet series defining the Dedekind zeta function is absolutely
summable throughout its classical half-plane `Re(s) > 1`. -/
theorem dedekindZeta_LSeriesSummable
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (fun n ↦ (Nat.card
        {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n} : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_
    (fun _ ↦ Nat.cast_nonneg _) zero_le_one hs
  exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by
    simpa [Real.rpow_one] using
      (((Ideal.tendsto_norm_le_div_atTop₀ K).comp
        tendsto_natCast_atTop_atTop).congr fun n ↦ by
          simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
          congr
          rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
            show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
            show 1 = Nat.card
                {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = 0} by
              simp [Ideal.absNorm_eq_zero_iff],
            Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
            ← Finset.card_preimage_eq_sum_card_image_eq
              (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
          simp [Set.coe_eq_subtype]))

/-- On `Re(s) > 1`, `dedekindZeta` is the sum of its absolutely convergent
ideal-count Dirichlet series. -/
theorem dedekindZeta_hasSum
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum
      (fun n ↦ (Nat.card
        {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n} : ℂ)) s
      (dedekindZeta K s) :=
  (dedekindZeta_LSeriesSummable K hs).LSeriesHasSum

end Convergence

end

end BealRegular.DedekindZetaEulerFoundations
