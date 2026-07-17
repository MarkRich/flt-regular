module

public import BealRegular.DedekindZetaEulerFoundations
public import BealRegular.MultisetEulerProduct
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# The Euler product for the Dedekind zeta function

For a number field `K` and `Re(s) > 1`, this file proves that `dedekindZeta K s`
is the convergent product of the geometric local factors indexed by the
height-one prime ideals of the ring of integers.  It also groups that product
fiberwise by the rational prime below each prime ideal.

The analytic input is the absolute convergence of the ideal-count Dirichlet
series from `DedekindZetaEulerFoundations`.  The algebraic input is that
nonzero ideals are finite multisets of height-one prime ideals.  The justified
infinite regrouping is supplied by `MultisetEulerProduct`.

Nothing here asserts analytic continuation or a cyclotomic factorization into
Dirichlet L-functions outside the half-plane of absolute convergence.
-/

@[expose] public section

open Filter Ideal NumberField Topology Asymptotics
open scoped BigOperators NumberField nonZeroDivisors Topology

noncomputable section

namespace BealRegular.DedekindZetaEulerProduct

open BealRegular.DedekindZetaEulerFoundations
open BealRegular.MultisetEulerProduct
open IsDedekindDomain

/-- Grouping ideals by their absolute norm. -/
private def idealNormSigmaEquiv
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] :
    Ideal R ≃ Σ n : ℕ, {I : Ideal R // absNorm I = n} where
  toFun I := ⟨absNorm I, ⟨I, rfl⟩⟩
  invFun z := z.2.1
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨n, I, hI⟩
    subst n
    rfl

/-- The L-series summand contributed by an ideal.  The zero ideal contributes
zero, exactly as the zeroth L-series term does. -/
private def idealLWeight
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R]
    (s : ℂ) (I : Ideal R) : ℂ :=
  LSeries.term (fun _ => (1 : ℂ)) s (absNorm I)

private theorem tsum_norm_idealLWeight_fiber
    (K : Type*) [Field K] [NumberField K] (s : ℂ) (n : ℕ) :
    (∑' I : {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n},
      ‖idealLWeight s I.1‖) =
      ‖LSeries.term
        (fun n => (Nat.card
          {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n} : ℂ))
        s n‖ := by
  letI : Finite
      {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n} :=
    Ideal.finite_setOf_absNorm_eq n
  letI := Fintype.ofFinite
    {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n}
  rw [tsum_fintype]
  have hterm (I :
      {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n}) :
      ‖idealLWeight s I.1‖ =
        ‖LSeries.term (fun _ => (1 : ℂ)) s n‖ := by
    rw [idealLWeight, I.property]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    LSeries.norm_term_eq, LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, Nat.card_eq_fintype_card, div_eq_mul_inv]

private theorem idealLWeight_norm_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun I : Ideal (NumberField.RingOfIntegers K) => ‖idealLWeight s I‖) := by
  let E := idealNormSigmaEquiv (NumberField.RingOfIntegers K)
  have houter : Summable (fun n : ℕ =>
      ∑' I : {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n},
        ‖idealLWeight s I.1‖) :=
    (dedekindZeta_LSeriesSummable K hs).norm.congr
      (fun n => (tsum_norm_idealLWeight_fiber K s n).symm)
  have hsigma : Summable (fun z : Σ n : ℕ,
      {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n} =>
        ‖idealLWeight s z.2.1‖) := by
    exact (summable_sigma_of_nonneg
      (f := fun z : Σ n : ℕ,
        {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n} =>
          ‖idealLWeight s z.2.1‖)
      (fun z => norm_nonneg (idealLWeight s z.2.1))).2
        ⟨fun n => by
          letI : Finite
              {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n} :=
            Ideal.finite_setOf_absNorm_eq n
          exact Summable.of_finite, houter⟩
  have hcomp := E.summable_iff.mpr hsigma
  simpa [E, Function.comp_def, idealNormSigmaEquiv] using hcomp

/-- The local Dirichlet-series variable attached to a height-one prime ideal. -/
private def primeLWeight (s : ℂ) {R : Type*}
    [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R]
    (v : HeightOneSpectrum R) : ℂ :=
  idealLWeight s v.asIdeal

private theorem primeLWeight_norm_summable
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      ‖primeLWeight s v‖) := by
  exact (idealLWeight_norm_summable K hs).comp_injective
    HeightOneSpectrum.asIdeal_injective

private theorem primeLWeight_eq_cpow
    (K : Type*) [Field K] [NumberField K] (s : ℂ)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    primeLWeight s v = (absNorm v.asIdeal : ℂ) ^ (-s) := by
  rw [primeLWeight, idealLWeight,
    LSeries.term_of_ne_zero (by
      exact Nat.ne_of_gt
        (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)))]
  simp [Complex.cpow_neg]

private theorem primeLWeight_norm_lt_one
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ‖primeLWeight s v‖ < 1 := by
  rw [primeLWeight_eq_cpow K s v, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg _) <|
      Complex.re_neg_ne_zero_of_one_lt_re hs, Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v) (by linarith)

private theorem prod_map_absNorm_cpow
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R]
    (s : ℂ) (m : Multiset (HeightOneSpectrum R)) :
    (m.map (fun v => (absNorm v.asIdeal : ℂ) ^ (-s))).prod =
      ((m.map (fun v => absNorm v.asIdeal)).prod : ℂ) ^ (-s) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons v m ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, ih, Nat.cast_mul]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
        Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

private theorem idealLWeight_nonzero
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R]
    (s : ℂ) (I : (Ideal R)⁰) :
    idealLWeight s (I : Ideal R) = (absNorm (I : Ideal R) : ℂ) ^ (-s) := by
  rw [idealLWeight,
    LSeries.term_of_ne_zero
      (Nat.ne_of_gt (Ideal.absNorm_pos_of_nonZeroDivisors I))]
  simp [Complex.cpow_neg]

private theorem multisetWeight_primeLWeight
    (K : Type*) [Field K] [NumberField K] (s : ℂ)
    (m : Multiset (HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    multisetWeight (primeLWeight s) m =
      idealLWeight s
        ((ofPrimeFactors (NumberField.RingOfIntegers K) m :
          (Ideal (NumberField.RingOfIntegers K))⁰) :
            Ideal (NumberField.RingOfIntegers K)) := by
  classical
  rw [multisetWeight_eq_prod_map]
  simp_rw [primeLWeight_eq_cpow K s]
  rw [prod_map_absNorm_cpow,
    ← absNorm_ofPrimeFactors (NumberField.RingOfIntegers K),
    ← idealLWeight_nonzero]

/-- Nonzero-divisor ideals are equivalent to ideals distinct from bottom. -/
private def nonzeroIdealEquivNeBot
    (R : Type*) [CommRing R] [IsDomain R] :
    (Ideal R)⁰ ≃ {I : Ideal R // I ≠ ⊥} where
  toFun I := ⟨I.1, nonZeroDivisors.coe_ne_zero I⟩
  invFun I := ⟨I.1, mem_nonZeroDivisors_of_ne_zero I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem tsum_idealLWeight_fiber
    (K : Type*) [Field K] [NumberField K] (s : ℂ) (n : ℕ) :
    (∑' I : {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n},
      idealLWeight s I.1) =
      LSeries.term
        (fun n => (Nat.card
          {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n} : ℂ))
        s n := by
  letI : Finite
      {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n} :=
    Ideal.finite_setOf_absNorm_eq n
  letI := Fintype.ofFinite
    {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n}
  rw [tsum_fintype]
  have hterm (I :
      {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n}) :
      idealLWeight s I.1 = LSeries.term (fun _ => (1 : ℂ)) s n := by
    rw [idealLWeight, I.property]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp [Nat.card_eq_fintype_card, div_eq_mul_inv]

private theorem tsum_idealLWeight_eq_dedekindZeta
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    (∑' I : Ideal (NumberField.RingOfIntegers K), idealLWeight s I) =
      dedekindZeta K s := by
  let E := idealNormSigmaEquiv (NumberField.RingOfIntegers K)
  have hi := (idealLWeight_norm_summable K hs).of_norm
  have hsigma : Summable (fun z : Σ n : ℕ,
      {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n} =>
        idealLWeight s z.2.1) := by
    have hcomp : Summable
        ((fun z : Σ n : ℕ,
          {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n} =>
            idealLWeight s z.2.1) ∘ E) := by
      simpa [E, Function.comp_def, idealNormSigmaEquiv] using hi
    exact E.summable_iff.mp hcomp
  calc
    (∑' I : Ideal (NumberField.RingOfIntegers K), idealLWeight s I) =
        ∑' z : Σ n : ℕ,
          {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n},
            idealLWeight s z.2.1 := by
          simpa [E, Function.comp_def, idealNormSigmaEquiv] using
            (E.tsum_eq (fun z : Σ n : ℕ,
              {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n} =>
                idealLWeight s z.2.1))
    _ = ∑' n : ℕ, ∑' I :
          {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n},
            idealLWeight s I.1 := hsigma.tsum_sigma
    _ = ∑' n : ℕ, LSeries.term
          (fun n => (Nat.card
            {I : Ideal (NumberField.RingOfIntegers K) // absNorm I = n} : ℂ))
          s n := by
            congr 1
            funext n
            exact tsum_idealLWeight_fiber K s n
    _ = dedekindZeta K s := by rfl

private theorem tsum_nonzeroIdeal_idealLWeight_eq_all
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    (∑' I : (Ideal (NumberField.RingOfIntegers K))⁰,
      idealLWeight s (I : Ideal (NumberField.RingOfIntegers K))) =
      ∑' I : Ideal (NumberField.RingOfIntegers K), idealLWeight s I := by
  let E := nonzeroIdealEquivNeBot (NumberField.RingOfIntegers K)
  calc
    (∑' I : (Ideal (NumberField.RingOfIntegers K))⁰,
      idealLWeight s (I : Ideal (NumberField.RingOfIntegers K))) =
        ∑' I : {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥},
          idealLWeight s I.1 := by
            simpa [E, Function.comp_def, nonzeroIdealEquivNeBot] using
              (E.tsum_eq (fun I :
                {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥} =>
                  idealLWeight s I.1))
    _ = ∑' I : Ideal (NumberField.RingOfIntegers K),
          Set.indicator
            {I : Ideal (NumberField.RingOfIntegers K) | I ≠ ⊥}
            (idealLWeight s) I := tsum_subtype _ _
    _ = ∑' I : Ideal (NumberField.RingOfIntegers K), idealLWeight s I := by
          apply tsum_congr
          intro I
          by_cases hI : I = ⊥
          · subst I
            simp [idealLWeight]
          · simp [Set.indicator, hI]

private theorem tsum_multisetWeight_primeLWeight_eq_dedekindZeta
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    (∑' m : Multiset (HeightOneSpectrum (NumberField.RingOfIntegers K)),
      multisetWeight (primeLWeight s) m) = dedekindZeta K s := by
  classical
  let E := (primeFactorsEquiv (NumberField.RingOfIntegers K)).symm
  calc
    (∑' m : Multiset (HeightOneSpectrum (NumberField.RingOfIntegers K)),
      multisetWeight (primeLWeight s) m) =
        ∑' I : (Ideal (NumberField.RingOfIntegers K))⁰,
          idealLWeight s (I : Ideal (NumberField.RingOfIntegers K)) := by
            simpa [E, Function.comp_def, primeFactorsEquiv,
              multisetWeight_primeLWeight] using
              (E.tsum_eq (fun I :
                (Ideal (NumberField.RingOfIntegers K))⁰ =>
                  idealLWeight s (I : Ideal (NumberField.RingOfIntegers K))))
    _ = ∑' I : Ideal (NumberField.RingOfIntegers K), idealLWeight s I :=
          tsum_nonzeroIdeal_idealLWeight_eq_all K s
    _ = dedekindZeta K s := tsum_idealLWeight_eq_dedekindZeta K hs

/-- The geometric Euler factor attached to one height-one prime ideal. -/
def dedekindPrimeIdealEulerFactor
    (K : Type*) [Field K] [NumberField K] (s : ℂ)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) : ℂ :=
  (1 - (absNorm v.asIdeal : ℂ) ^ (-s))⁻¹

/-- On `Re(s) > 1`, the Dedekind zeta function is the convergent Euler product
over the height-one prime ideals of the ring of integers. -/
theorem dedekindZeta_eulerProduct_hasProd
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    HasProd (dedekindPrimeIdealEulerFactor K s) (dedekindZeta K s) := by
  classical
  have hp := hasProd_geometric_eq_tsum_multiset
    (primeLWeight s) (primeLWeight_norm_summable K hs)
      (primeLWeight_norm_lt_one K hs)
  rw [tsum_multisetWeight_primeLWeight_eq_dedekindZeta K hs] at hp
  change HasProd
    (fun v : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      (1 - (absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
    (dedekindZeta K s)
  simpa only [primeLWeight_eq_cpow K s] using hp

/-- The rational prime lying below a height-one prime of the ring of integers. -/
def rationalPrimeBelow
    (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) : Nat.Primes :=
  Rat.HeightOneSpectrum.primesEquiv (v.under ℤ)

/-- Under the rational-prime equivalence, the inverse image of `q` has
underlying ideal generated by `q`. -/
theorem rationalPrimeIdeal_asIdeal_eq_span (q : Nat.Primes) :
    ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm q).asIdeal =
      Ideal.span {((q : ℕ) : ℤ)} := by
  have he : Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ := by
    ext n
    simp
  simp only [Rat.HeightOneSpectrum.primesEquiv, he]
  change Ideal.map (RingHom.id ℤ) (Ideal.span {((q : ℕ) : ℤ)}) =
    Ideal.span {((q : ℕ) : ℤ)}
  exact Ideal.map_id _

/-- A member of the fiber above `q` lies over the ideal generated by `q`. -/
theorem rationalPrimeBelow_fiber_under_eq_span
    (K : Type*) [Field K] [NumberField K] (q : Nat.Primes)
    (v : rationalPrimeBelow K ⁻¹' {q}) :
    v.1.asIdeal.under ℤ = Ideal.span {((q : ℕ) : ℤ)} := by
  have hq : Rat.HeightOneSpectrum.primesEquiv (v.1.under ℤ) = q := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, rationalPrimeBelow] using v.property
  have hunder : v.1.under ℤ =
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm q := by
    apply Rat.HeightOneSpectrum.primesEquiv.injective
    simpa only [Equiv.apply_symm_apply] using hq
  calc
    v.1.asIdeal.under ℤ = (v.1.under ℤ).asIdeal := rfl
    _ = ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm q).asIdeal :=
      congrArg HeightOneSpectrum.asIdeal hunder
    _ = Ideal.span {((q : ℕ) : ℤ)} := rationalPrimeIdeal_asIdeal_eq_span q

/-- A prime ideal in the fiber above `q`, viewed as an element of Mathlib's
`primesOver (span {q})` set. -/
def rationalFiberToPrimesOverSpan
    (K : Type*) [Field K] [NumberField K] (q : Nat.Primes) :
    rationalPrimeBelow K ⁻¹' {q} →
      (Ideal.span {((q : ℕ) : ℤ)}).primesOver
        (NumberField.RingOfIntegers K) := fun v =>
  ⟨v.1.asIdeal, v.1.isPrime,
    { over := (rationalPrimeBelow_fiber_under_eq_span K q v).symm }⟩

@[simp]
theorem rationalFiberToPrimesOverSpan_apply
    (K : Type*) [Field K] [NumberField K] (q : Nat.Primes)
    (v : rationalPrimeBelow K ⁻¹' {q}) :
    (rationalFiberToPrimesOverSpan K q v :
      Ideal (NumberField.RingOfIntegers K)) = v.1.asIdeal := rfl

theorem rationalFiberToPrimesOverSpan_injective
    (K : Type*) [Field K] [NumberField K] (q : Nat.Primes) :
    Function.Injective (rationalFiberToPrimesOverSpan K q) := by
  intro v w hvw
  apply Subtype.ext
  apply HeightOneSpectrum.asIdeal_injective
  exact congrArg Subtype.val hvw

theorem rationalFiberToPrimesOverSpan_surjective
    (K : Type*) [Field K] [NumberField K] (q : Nat.Primes) :
    Function.Surjective (rationalFiberToPrimesOverSpan K q) := by
  intro P
  have hp : Ideal.span {((q : ℕ) : ℤ)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast q.2.ne_zero
  let v : HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    ⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver hp P.2⟩
  have hv_under : v.under ℤ =
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm q := by
    apply HeightOneSpectrum.asIdeal_injective
    calc
      (v.under ℤ).asIdeal = P.1.under ℤ := rfl
      _ = Ideal.span {((q : ℕ) : ℤ)} :=
        (Ideal.LiesOver.over (p := Ideal.span {((q : ℕ) : ℤ)}) (P := P.1)).symm
      _ = ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm q).asIdeal :=
        (rationalPrimeIdeal_asIdeal_eq_span q).symm
  have hvq : rationalPrimeBelow K v = q := by
    change Rat.HeightOneSpectrum.primesEquiv (v.under ℤ) = q
    rw [hv_under, Equiv.apply_symm_apply]
  let w : rationalPrimeBelow K ⁻¹' {q} :=
    ⟨v, by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hvq⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  rfl

/-- Prime ideals in the fiber above `q` are exactly the prime ideals lying
over the principal ideal generated by `q`. -/
def rationalFiberEquivPrimesOverSpan
    (K : Type*) [Field K] [NumberField K] (q : Nat.Primes) :
    rationalPrimeBelow K ⁻¹' {q} ≃
      (Ideal.span {((q : ℕ) : ℤ)}).primesOver
        (NumberField.RingOfIntegers K) :=
  Equiv.ofBijective (rationalFiberToPrimesOverSpan K q)
    ⟨rationalFiberToPrimesOverSpan_injective K q,
      rationalFiberToPrimesOverSpan_surjective K q⟩

@[simp]
theorem rationalFiberEquivPrimesOverSpan_apply
    (K : Type*) [Field K] [NumberField K] (q : Nat.Primes)
    (v : rationalPrimeBelow K ⁻¹' {q}) :
    (rationalFiberEquivPrimesOverSpan K q v :
      Ideal (NumberField.RingOfIntegers K)) = v.1.asIdeal := rfl

/-- There are only finitely many prime ideals above each rational prime. -/
theorem rationalPrimeBelow_finite_fiber
    (K : Type*) [Field K] [NumberField K] (q : Nat.Primes) :
    Finite (rationalPrimeBelow K ⁻¹' {q}) := by
  letI : Fintype
      ((Ideal.span {((q : ℕ) : ℤ)}).primesOver
        (NumberField.RingOfIntegers K)) := by
    rw [← rationalPrimeIdeal_asIdeal_eq_span q]
    infer_instance
  exact Finite.of_injective (rationalFiberToPrimesOverSpan K q)
    (rationalFiberToPrimesOverSpan_injective K q)

/-- The product of the prime-ideal Euler factors above one rational prime. -/
def dedekindRationalLocalFactor
    (K : Type*) [Field K] [NumberField K] (s : ℂ) (q : Nat.Primes) : ℂ :=
  ∏' v : rationalPrimeBelow K ⁻¹' {q},
    dedekindPrimeIdealEulerFactor K s v.1

private theorem dedekindZeta_rationalEulerProduct_hasProd_aux
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    HasProd (dedekindRationalLocalFactor K s) (dedekindZeta K s) := by
  have htotal : HasProd
      ((dedekindPrimeIdealEulerFactor K s) ∘
        Equiv.sigmaFiberEquiv (rationalPrimeBelow K))
      (dedekindZeta K s) :=
    (Equiv.sigmaFiberEquiv (rationalPrimeBelow K)).hasProd_iff.mpr
      (dedekindZeta_eulerProduct_hasProd K hs)
  apply htotal.sigma
  intro q
  letI : Finite (rationalPrimeBelow K ⁻¹' {q}) :=
    rationalPrimeBelow_finite_fiber K q
  change HasProd
    (fun v : rationalPrimeBelow K ⁻¹' {q} =>
      dedekindPrimeIdealEulerFactor K s v.1)
    (∏' v : rationalPrimeBelow K ⁻¹' {q},
      dedekindPrimeIdealEulerFactor K s v.1)
  exact Multipliable.of_finite.hasProd

/-- On `Re(s) > 1`, the Dedekind zeta Euler product may be grouped by the
rational prime below each prime ideal. -/
theorem dedekindZeta_rationalEulerProduct_hasProd
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    HasProd (dedekindRationalLocalFactor K s) (dedekindZeta K s) :=
  dedekindZeta_rationalEulerProduct_hasProd_aux K hs

end BealRegular.DedekindZetaEulerProduct
