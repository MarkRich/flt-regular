import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Weighted polynomial root scaling

This module supplies generic coefficient algebra for integrally rescaling a
polynomial factor.  If `P = f * g`, the constant coefficient of `f` is a
unit, and the coefficients of `P` below a cutoff lie in complementary powers
of an ideal, then the corresponding coefficients of `g` lie in the same
powers.  For a principal ideal `(s)`, those divisibilities construct a monic
polynomial `q` such that `q.scaleRoots s = g`.  A fixed-ideal variant preserves
uniform coefficient bounds, and cancellation in a domain tracks the powers
left in coefficients after descaling.

Over any coefficient ring where `s` is a unit, scaling roots by `s` gives an
explicit equivalence of the corresponding adjoin-root algebras.  These
statements are the generic algebraic input for rescaling the small signature
`(3,5,7)` factors.  They do not establish a factorization, assert uniqueness
when `s` is zero or a zero divisor, give an integral algebra equivalence for a
nonunit `s`, identify a residual model, prove etaleness or ramification
properties, exclude signature `(3,5,7)`, or prove Beal's conjecture.
-/

namespace BealRegular.WeightedPolynomialScaling

open Polynomial

noncomputable section

universe u v

variable {R : Type u} [CommRing R]

/-- Dividing by a factor with unit constant coefficient preserves the
complementary-power filtration on all coefficients below a chosen cutoff. -/
theorem weightedCoeff_mem_of_mul_eq_of_constantCoeff_isUnit
    (I : Ideal R) {n : ℕ} (P f g : R[X])
    (hfac : P = f * g) (hf0 : IsUnit (f.coeff 0))
    (hP : ∀ i < n, P.coeff i ∈ I ^ (n - i)) :
    ∀ i < n, g.coeff i ∈ I ^ (n - i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi
      let J := I ^ (n - i)
      have hprod : (f * g).coeff i ∈ J := by
        rw [← hfac]
        exact hP i hi
      rw [coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ'] at hprod
      simp only [Nat.sub_zero] at hprod
      have htail :
          ∑ k ∈ Finset.range i, f.coeff (k + 1) * g.coeff (i - (k + 1)) ∈ J := by
        apply J.sum_mem
        intro k hk
        have hklt : k < i := Finset.mem_range.mp hk
        have hidx : i - (k + 1) < i := by omega
        have hg : g.coeff (i - (k + 1)) ∈ I ^ (n - (i - (k + 1))) :=
          ih (i - (k + 1)) hidx (by omega)
        have hexp : n - i ≤ n - (i - (k + 1)) := by omega
        exact J.mul_mem_left _ (Ideal.pow_le_pow_right hexp hg)
      have hunitprod : f.coeff 0 * g.coeff i ∈ J := by
        simpa [add_sub_cancel_left] using J.sub_mem hprod htail
      exact (Ideal.unit_mul_mem_iff_mem J hf0).mp hunitprod

/-- Dividing by a factor with unit constant coefficient preserves membership
in a fixed ideal for every coefficient below an arbitrary cutoff. -/
theorem lowCoeffs_mem_of_mul_eq_of_constantCoeff_isUnit
    (I : Ideal R) {n : ℕ} (P f g : R[X])
    (hfac : P = f * g) (hf0 : IsUnit (f.coeff 0))
    (hP : ∀ i < n, P.coeff i ∈ I) :
    ∀ i < n, g.coeff i ∈ I := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi
      have hprod : (f * g).coeff i ∈ I := by
        rw [← hfac]
        exact hP i hi
      rw [coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ'] at hprod
      simp only [Nat.sub_zero] at hprod
      have htail :
          ∑ k ∈ Finset.range i, f.coeff (k + 1) * g.coeff (i - (k + 1)) ∈ I := by
        apply I.sum_mem
        intro k hk
        have hklt : k < i := Finset.mem_range.mp hk
        have hidx : i - (k + 1) < i := by omega
        exact I.mul_mem_left _ (ih (i - (k + 1)) hidx (by omega))
      have hunitprod : f.coeff 0 * g.coeff i ∈ I := by
        simpa [add_sub_cancel_left] using I.sub_mem hprod htail
      exact (Ideal.unit_mul_mem_iff_mem I hf0).mp hunitprod

/-- If a degree-`n` polynomial `G` descales `g` through `scaleRoots q`, then
full `q ^ n` divisibility of a low coefficient of `g` leaves `q ^ i`
divisibility in the corresponding coefficient of `G`. -/
theorem pow_dvd_descaled_coeff_of_scaleRoots_eq [IsDomain R]
    {n i : ℕ} (G g : R[X]) (q : R)
    (hGdeg : G.natDegree = n) (hscale : G.scaleRoots q = g)
    (hq : q ≠ 0) (hi : i < n) (hdiv : q ^ n ∣ g.coeff i) :
    q ^ i ∣ G.coeff i := by
  have hdiv' : q ^ n ∣ G.coeff i * q ^ (n - i) := by
    rw [← hscale, coeff_scaleRoots, hGdeg] at hdiv
    exact hdiv
  have hpow : q ^ n = q ^ (n - i) * q ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi.le]
  rw [hpow, mul_comm (G.coeff i) (q ^ (n - i))] at hdiv'
  exact (mul_dvd_mul_iff_left (pow_ne_zero (n - i) hq)).mp hdiv'

variable [Nontrivial R]

/-- Coefficientwise divisibility by the complementary powers of `s` is
sufficient to descend a monic polynomial through `Polynomial.scaleRoots`. -/
theorem exists_monicDegreeEq_scaleRoots_eq_of_weightedDvd
    {n : ℕ} (p : MonicDegreeEq R n) (s : R)
    (hdiv : ∀ i < n, s ^ (n - i) ∣ p.1.coeff i) :
    ∃ q : MonicDegreeEq R n, q.1.scaleRoots s = p.1 := by
  classical
  let c : (i : ℕ) → i < n → R := fun i hi ↦ (hdiv i hi).choose
  have hc : ∀ (i : ℕ) (hi : i < n),
      p.1.coeff i = c i hi * s ^ (n - i) := by
    intro i hi
    simpa [c, mul_comm] using (hdiv i hi).choose_spec
  let qpoly : R[X] :=
    ∑ i ∈ Finset.range n, monomial i (if hi : i < n then c i hi else 0) + X ^ n
  have hqcoeff_lt : ∀ (i : ℕ) (hi : i < n), qpoly.coeff i = c i hi := by
    intro i hi
    simp only [qpoly, coeff_add, finsetSum_coeff, coeff_monomial, coeff_X_pow]
    rw [Finset.sum_eq_single i]
    · simp [hi, Nat.ne_of_lt hi]
    · intro b hb hbi
      simp [hbi]
    · exact fun h ↦ (h (Finset.mem_range.mpr hi)).elim
  have hqcoeff_eq : qpoly.coeff n = 1 := by
    simp +contextual [qpoly, coeff_monomial]
  have hqcoeff_gt : ∀ i > n, qpoly.coeff i = 0 := by
    intro i hi
    have hnot : ¬ i < n := Nat.not_lt_of_ge hi.le
    have hne : i ≠ n := Nat.ne_of_gt hi
    simp +contextual [qpoly, coeff_monomial, hnot, hne]
  let q : MonicDegreeEq R n := ⟨qpoly, hqcoeff_eq, hqcoeff_gt⟩
  refine ⟨q, ?_⟩
  ext i
  rw [coeff_scaleRoots, q.natDegree]
  change qpoly.coeff i * s ^ (n - i) = p.1.coeff i
  rcases lt_trichotomy i n with hin | rfl | hin
  · rw [hqcoeff_lt i hin, hc i hin]
  · rw [hqcoeff_eq, p.2.1]
    simp
  · rw [hqcoeff_gt i hin, p.2.2 i hin]
    simp

/-- Ideal-power form of the weighted divisibility criterion. -/
theorem exists_monicDegreeEq_scaleRoots_eq_of_mem_span_pow
    {n : ℕ} (p : MonicDegreeEq R n) (s : R)
    (hmem : ∀ i < n, p.1.coeff i ∈ (Ideal.span {s}) ^ (n - i)) :
    ∃ q : MonicDegreeEq R n, q.1.scaleRoots s = p.1 := by
  apply exists_monicDegreeEq_scaleRoots_eq_of_weightedDvd p s
  intro i hi
  have h := hmem i hi
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  exact h

variable {K : Type v} [CommRing K]

/-- Scaling roots by a unit does not change the quotient algebra.  This
equivalence sends the root of `p.scaleRoots s` to `s` times the root of `p`. -/
def adjoinRootScaleRootsAlgEquiv (p : K[X]) (s : K) (hs : IsUnit s) :
    AdjoinRoot (p.scaleRoots s) ≃ₐ[K] AdjoinRoot p := by
  let t : K := ↑(hs.unit⁻¹)
  have hst : s * t = 1 := by
    rw [← hs.unit_spec]
    simp [t]
  have hts : t * s = 1 := by
    rw [← hs.unit_spec]
    simp [t]
  have hforward :
      (p.scaleRoots s).eval₂ (AdjoinRoot.of p)
          (AdjoinRoot.of p s * AdjoinRoot.root p) = 0 :=
    scaleRoots_eval₂_eq_zero (AdjoinRoot.of p) (AdjoinRoot.eval₂_root p)
  let forward : AdjoinRoot (p.scaleRoots s) →ₐ[K] AdjoinRoot p :=
    AdjoinRoot.liftAlgHom (p.scaleRoots s) (Algebra.ofId K (AdjoinRoot p))
      (AdjoinRoot.of p s * AdjoinRoot.root p) hforward
  have hscale : (p.scaleRoots s).scaleRoots t = p := by
    rw [← scaleRoots_mul, hst, scaleRoots_one]
  have hbackward :
      p.eval₂ (AdjoinRoot.of (p.scaleRoots s))
          (AdjoinRoot.of (p.scaleRoots s) t *
            AdjoinRoot.root (p.scaleRoots s)) = 0 := by
    have h := scaleRoots_eval₂_eq_zero
      (p := p.scaleRoots s) (f := AdjoinRoot.of (p.scaleRoots s)) (s := t)
      (AdjoinRoot.eval₂_root (p.scaleRoots s))
    rwa [hscale] at h
  let backward : AdjoinRoot p →ₐ[K] AdjoinRoot (p.scaleRoots s) :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId K (AdjoinRoot (p.scaleRoots s)))
      (AdjoinRoot.of (p.scaleRoots s) t *
        AdjoinRoot.root (p.scaleRoots s)) hbackward
  exact AlgEquiv.ofAlgHom forward backward
    (by
      apply AdjoinRoot.algHom_ext
      change forward (backward (AdjoinRoot.root p)) = AdjoinRoot.root p
      rw [AdjoinRoot.liftAlgHom_root, map_mul]
      have hcoeff := forward.commutes t
      rw [AdjoinRoot.algebraMap_eq] at hcoeff
      rw [hcoeff, AdjoinRoot.liftAlgHom_root, AdjoinRoot.algebraMap_eq,
        ← mul_assoc, ← map_mul, hts, map_one, one_mul])
    (by
      apply AdjoinRoot.algHom_ext
      change backward (forward (AdjoinRoot.root (p.scaleRoots s))) =
        AdjoinRoot.root (p.scaleRoots s)
      rw [AdjoinRoot.liftAlgHom_root, map_mul]
      have hcoeff := backward.commutes s
      rw [AdjoinRoot.algebraMap_eq] at hcoeff
      rw [hcoeff, AdjoinRoot.liftAlgHom_root, AdjoinRoot.algebraMap_eq,
        ← mul_assoc, ← map_mul, hst, map_one, one_mul])

@[simp]
theorem adjoinRootScaleRootsAlgEquiv_root (p : K[X]) (s : K) (hs : IsUnit s) :
    adjoinRootScaleRootsAlgEquiv p s hs (AdjoinRoot.root (p.scaleRoots s)) =
      algebraMap K (AdjoinRoot p) s * AdjoinRoot.root p := by
  simp [adjoinRootScaleRootsAlgEquiv]

end

end BealRegular.WeightedPolynomialScaling
