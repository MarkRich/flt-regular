import BealRegular.DedekindZetaEulerProduct
import BealRegular.TwentyThreeRealPrimeDecomposition
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Dedekind local-factor identities at 23

This file evaluates the full cyclotomic and maximal-real Dedekind local
factors at every unramified rational prime.  It then proves that the two local
factors agree at the ramified prime `23`, where every odd
Dirichlet-character factor is one.  The global Euler-product assembly is kept
separately in `TwentyThreeGlobalFactorization`.
-/

open scoped BigOperators NumberField LSeries.notation

namespace BealRegular.TwentyThreeDedekindLocalFactors

open DirichletCharacter
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open IsDedekindDomain
open BealRegular.DedekindZetaEulerProduct

noncomputable section

local notation "K23" => CyclotomicField 23 ℚ
local notation "K23plus" => NumberField.maximalRealSubfield K23

local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

local instance : IsCyclotomicExtension {23} ℚ K23 :=
  CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero 23 ℚ

local instance : IsGalois ℚ K23 :=
  IsCyclotomicExtension.isGalois {23} ℚ K23

local instance : IsGalois ℚ K23plus :=
  BealRegular.TwentyThreeRealSubfieldClassNumber.maximalRealSubfield_isGalois

local instance : NumberField.IsCMField K23 :=
  BealRegular.TwentyThreeRealSubfield.cyclotomicFieldTwentyThree_isCMField

/-! ## Finite odd-character factors -/

/-- The product of the eleven odd-character Euler factors at a formal local
variable `X`. -/
def oddCharacterLocalFactorX (a : ZMod 23) (X : ℂ) : ℂ :=
  ∏ χ ∈ BealRegular.oddCharacters23, (1 - χ a * X)⁻¹

/-- The product of character factors is the inverse of the evaluated local
Euler polynomial. -/
theorem oddCharacterLocalFactorX_eq_eval_inv (a : ZMod 23) (X : ℂ) :
    oddCharacterLocalFactorX a X =
      (Polynomial.eval X
        (BealRegular.oddCharacterEulerPolynomialTwentyThree a))⁻¹ := by
  classical
  rw [oddCharacterLocalFactorX,
    BealRegular.oddCharacterEulerPolynomialTwentyThree,
    Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Finset.prod_inv_distrib]

/-- Raising a rational prime before taking a complex power is the same as
raising its local variable to that natural power. -/
theorem nat_pow_cpow_neg (q f : ℕ) (s : ℂ) :
    ((q ^ f : ℕ) : ℂ) ^ (-s) = ((q : ℂ) ^ (-s)) ^ f := by
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
  exact Complex.cpow_nat_mul (q : ℂ) f (-s)

/-- The polynomial local denominator identities remain valid after evaluation
and inversion, in exactly the form used by Euler products. -/
theorem evaluated_localFactor_prime_order_cases
    {q : ℕ} (hq : Nat.Prime q) (hq23 : q ≠ 23) (X : ℂ) :
    (orderOf (q : ZMod 23) = 1 ∧
      ((1 - X) ^ 22)⁻¹ =
        ((1 - X) ^ 11)⁻¹ * oddCharacterLocalFactorX q X) ∨
    (orderOf (q : ZMod 23) = 2 ∧
      ((1 - X ^ 2) ^ 11)⁻¹ =
        ((1 - X) ^ 11)⁻¹ * oddCharacterLocalFactorX q X) ∨
    (orderOf (q : ZMod 23) = 11 ∧
      ((1 - X ^ 11) ^ 2)⁻¹ =
        (1 - X ^ 11)⁻¹ * oddCharacterLocalFactorX q X) ∨
    (orderOf (q : ZMod 23) = 22 ∧
      (1 - X ^ 22)⁻¹ =
        (1 - X ^ 11)⁻¹ * oddCharacterLocalFactorX q X) := by
  have hcases :=
    BealRegular.cyclotomicRealOdd_localEulerFactor_prime_order_cases hq hq23
  rw [oddCharacterLocalFactorX_eq_eval_inv]
  rcases hcases with h1 | h2 | h11 | h22
  · refine Or.inl ⟨h1.1, ?_⟩
    have heval := congrArg (Polynomial.eval X) h1.2
    simpa only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_X, Polynomial.eval_mul, mul_inv_rev, mul_comm] using
        congrArg Inv.inv heval
  · refine Or.inr (Or.inl ⟨h2.1, ?_⟩)
    have heval := congrArg (Polynomial.eval X) h2.2
    simpa only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_mul, mul_inv_rev,
      mul_comm] using
        congrArg Inv.inv heval
  · refine Or.inr (Or.inr (Or.inl ⟨h11.1, ?_⟩))
    have heval := congrArg (Polynomial.eval X) h11.2
    simpa only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_X, Polynomial.eval_mul, mul_inv_rev, mul_comm] using
        congrArg Inv.inv heval
  · refine Or.inr (Or.inr (Or.inr ⟨h22.1, ?_⟩))
    have heval := congrArg (Polynomial.eval X) h22.2
    simpa only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_X, Polynomial.eval_mul, mul_inv_rev, mul_comm] using
        congrArg Inv.inv heval

/-! ## Dedekind local factors -/

/-- A rational local Dedekind factor is determined by the common residue
degree and the number of primes above the rational prime. -/
theorem dedekindRationalLocalFactor_eq_of_inertia_ncard
    (K : Type*) [Field K] [NumberField K]
    (s : ℂ) (q : Nat.Primes) (f g : ℕ)
    (hinertia : ∀ P : Ideal.primesOver (Ideal.span {((q : ℕ) : ℤ)})
      (NumberField.RingOfIntegers K),
        (P : Ideal (NumberField.RingOfIntegers K)).inertiaDeg ℤ = f)
    (hncard : (Ideal.primesOver (Ideal.span {((q : ℕ) : ℤ)})
      (NumberField.RingOfIntegers K)).ncard = g) :
    dedekindRationalLocalFactor K s q =
      (((1 - (((q : ℕ) : ℂ) ^ (-s)) ^ f) ^ g)⁻¹) := by
  let E := rationalFiberEquivPrimesOverSpan K q
  letI : Finite (rationalPrimeBelow K ⁻¹' {q}) :=
    rationalPrimeBelow_finite_fiber K q
  letI : Fintype (rationalPrimeBelow K ⁻¹' {q}) := Fintype.ofFinite _
  have hfactor (v : rationalPrimeBelow K ⁻¹' {q}) :
      dedekindPrimeIdealEulerFactor K s v.1 =
        (1 - (((q : ℕ) : ℂ) ^ (-s)) ^ f)⁻¹ := by
    let P := E v
    letI : (P : Ideal (NumberField.RingOfIntegers K)).IsPrime := P.property.1
    letI : (P : Ideal (NumberField.RingOfIntegers K)).LiesOver
        (Ideal.span {((q : ℕ) : ℤ)}) := P.property.2
    have hnorm : Ideal.absNorm v.1.asIdeal = (q : ℕ) ^ f := by
      calc
        Ideal.absNorm v.1.asIdeal =
            Ideal.absNorm (P : Ideal (NumberField.RingOfIntegers K)) := by
              rw [show (P : Ideal (NumberField.RingOfIntegers K)) =
                v.1.asIdeal by rfl]
        _ = (q : ℕ) ^
            (P : Ideal (NumberField.RingOfIntegers K)).inertiaDeg ℤ := by
              symm
              exact Ideal.pow_inertiaDeg (q : ℕ)
                (P : Ideal (NumberField.RingOfIntegers K))
        _ = (q : ℕ) ^ f := by rw [hinertia P]
    rw [dedekindPrimeIdealEulerFactor, hnorm, nat_pow_cpow_neg]
  rw [dedekindRationalLocalFactor, tprod_fintype]
  simp_rw [hfactor]
  rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    Nat.card_congr E, Nat.card_coe_set_eq, hncard, inv_pow]

/-- The four unramified local factors for the full cyclotomic field. -/
theorem cyclotomic_dedekindRationalLocalFactor_prime_order_cases
    (s : ℂ) {q : ℕ} (hq : Nat.Prime q) (hq23 : q ≠ 23) :
    (orderOf (q : ZMod 23) = 1 ∧
      dedekindRationalLocalFactor K23 s ⟨q, hq⟩ =
        ((1 - (q : ℂ) ^ (-s)) ^ 22)⁻¹) ∨
    (orderOf (q : ZMod 23) = 2 ∧
      dedekindRationalLocalFactor K23 s ⟨q, hq⟩ =
        ((1 - ((q : ℂ) ^ (-s)) ^ 2) ^ 11)⁻¹) ∨
    (orderOf (q : ZMod 23) = 11 ∧
      dedekindRationalLocalFactor K23 s ⟨q, hq⟩ =
        ((1 - ((q : ℂ) ^ (-s)) ^ 11) ^ 2)⁻¹) ∨
    (orderOf (q : ZMod 23) = 22 ∧
      dedekindRationalLocalFactor K23 s ⟨q, hq⟩ =
        (1 - ((q : ℂ) ^ (-s)) ^ 22)⁻¹) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hnot : ¬ q ∣ 23 := by
    intro hdvd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 23)).mp hdvd with hq1 | hqeq
    · exact hq.ne_one hq1
    · exact hq23 hqeq
  have hinertia (P : Ideal.primesOver (Ideal.span {(q : ℤ)})
      (NumberField.RingOfIntegers K23)) :
      (P : Ideal (NumberField.RingOfIntegers K23)).inertiaDeg ℤ =
        orderOf (q : ZMod 23) := by
    letI : (P : Ideal (NumberField.RingOfIntegers K23)).IsPrime := P.property.1
    letI : (P : Ideal (NumberField.RingOfIntegers K23)).LiesOver
        (Ideal.span {(q : ℤ)}) := P.property.2
    exact IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd q K23 P hnot
  have hncard := BealRegular.cyclotomic23_ncard_primesOver_mul_orderOf hq hq23
  have horders :=
    BealRegular.oddCharacterEulerPolynomialTwentyThree_prime_order_cases hq hq23
  rcases horders with h1 | h2 | h11 | h22
  · have hg : (Ideal.primesOver (Ideal.span {(q : ℤ)})
        (NumberField.RingOfIntegers K23)).ncard = 22 := by
      rw [h1.1, mul_one] at hncard
      exact hncard
    have hlocal := dedekindRationalLocalFactor_eq_of_inertia_ncard
      K23 s ⟨q, hq⟩ 1 22 (fun P => by rw [hinertia P, h1.1]) hg
    exact Or.inl ⟨h1.1, by simpa using hlocal⟩
  · have hg : (Ideal.primesOver (Ideal.span {(q : ℤ)})
        (NumberField.RingOfIntegers K23)).ncard = 11 := by
      rw [h2.1] at hncard
      omega
    have hlocal := dedekindRationalLocalFactor_eq_of_inertia_ncard
      K23 s ⟨q, hq⟩ 2 11 (fun P => by rw [hinertia P, h2.1]) hg
    exact Or.inr (Or.inl ⟨h2.1, by simpa using hlocal⟩)
  · have hg : (Ideal.primesOver (Ideal.span {(q : ℤ)})
        (NumberField.RingOfIntegers K23)).ncard = 2 := by
      rw [h11.1] at hncard
      omega
    have hlocal := dedekindRationalLocalFactor_eq_of_inertia_ncard
      K23 s ⟨q, hq⟩ 11 2 (fun P => by rw [hinertia P, h11.1]) hg
    exact Or.inr (Or.inr (Or.inl ⟨h11.1, by simpa using hlocal⟩))
  · have hg : (Ideal.primesOver (Ideal.span {(q : ℤ)})
        (NumberField.RingOfIntegers K23)).ncard = 1 := by
      rw [h22.1] at hncard
      omega
    have hlocal := dedekindRationalLocalFactor_eq_of_inertia_ncard
      K23 s ⟨q, hq⟩ 22 1 (fun P => by rw [hinertia P, h22.1]) hg
    exact Or.inr (Or.inr (Or.inr ⟨h22.1, by simpa using hlocal⟩))

/-- The four unramified local factors for the maximal real subfield. -/
theorem real_dedekindRationalLocalFactor_prime_order_cases
    (s : ℂ) {q : ℕ} (hq : Nat.Prime q) (hq23 : q ≠ 23) :
    (orderOf (q : ZMod 23) = 1 ∧
      dedekindRationalLocalFactor K23plus s ⟨q, hq⟩ =
        ((1 - (q : ℂ) ^ (-s)) ^ 11)⁻¹) ∨
    (orderOf (q : ZMod 23) = 2 ∧
      dedekindRationalLocalFactor K23plus s ⟨q, hq⟩ =
        ((1 - (q : ℂ) ^ (-s)) ^ 11)⁻¹) ∨
    (orderOf (q : ZMod 23) = 11 ∧
      dedekindRationalLocalFactor K23plus s ⟨q, hq⟩ =
        (1 - ((q : ℂ) ^ (-s)) ^ 11)⁻¹) ∨
    (orderOf (q : ZMod 23) = 22 ∧
      dedekindRationalLocalFactor K23plus s ⟨q, hq⟩ =
        (1 - ((q : ℂ) ^ (-s)) ^ 11)⁻¹) := by
  have hncases :=
    BealRegular.TwentyThreeRealPrimeDecomposition.realSubfield_ncard_primesOver_order_cases
      hq hq23
  rcases hncases with h1 | h2 | h11 | h22
  · have hinertia : ∀ P : Ideal.primesOver (Ideal.span {(q : ℤ)})
        (NumberField.RingOfIntegers K23plus),
        (P : Ideal (NumberField.RingOfIntegers K23plus)).inertiaDeg ℤ = 1 := by
      intro P
      rcases BealRegular.TwentyThreeRealPrimeDecomposition.realSubfield_inertiaDeg_order_cases
          hq hq23 P with
        c1 | c2 | c11 | c22
      · exact c1.2
      all_goals omega
    have hlocal := dedekindRationalLocalFactor_eq_of_inertia_ncard
      K23plus s ⟨q, hq⟩ 1 11 hinertia h1.2
    exact Or.inl ⟨h1.1, by simpa using hlocal⟩
  · have hinertia : ∀ P : Ideal.primesOver (Ideal.span {(q : ℤ)})
        (NumberField.RingOfIntegers K23plus),
        (P : Ideal (NumberField.RingOfIntegers K23plus)).inertiaDeg ℤ = 1 := by
      intro P
      rcases BealRegular.TwentyThreeRealPrimeDecomposition.realSubfield_inertiaDeg_order_cases
          hq hq23 P with
        c1 | c2 | c11 | c22
      · omega
      · exact c2.2
      all_goals omega
    have hlocal := dedekindRationalLocalFactor_eq_of_inertia_ncard
      K23plus s ⟨q, hq⟩ 1 11 hinertia h2.2
    exact Or.inr (Or.inl ⟨h2.1, by simpa using hlocal⟩)
  · have hinertia : ∀ P : Ideal.primesOver (Ideal.span {(q : ℤ)})
        (NumberField.RingOfIntegers K23plus),
        (P : Ideal (NumberField.RingOfIntegers K23plus)).inertiaDeg ℤ = 11 := by
      intro P
      rcases BealRegular.TwentyThreeRealPrimeDecomposition.realSubfield_inertiaDeg_order_cases
          hq hq23 P with
        c1 | c2 | c11 | c22
      · omega
      · omega
      · exact c11.2
      · omega
    have hlocal := dedekindRationalLocalFactor_eq_of_inertia_ncard
      K23plus s ⟨q, hq⟩ 11 1 hinertia h11.2
    exact Or.inr (Or.inr (Or.inl ⟨h11.1, by simpa using hlocal⟩))
  · have hinertia : ∀ P : Ideal.primesOver (Ideal.span {(q : ℤ)})
        (NumberField.RingOfIntegers K23plus),
        (P : Ideal (NumberField.RingOfIntegers K23plus)).inertiaDeg ℤ = 11 := by
      intro P
      rcases BealRegular.TwentyThreeRealPrimeDecomposition.realSubfield_inertiaDeg_order_cases
          hq hq23 P with
        c1 | c2 | c11 | c22
      all_goals omega
    have hlocal := dedekindRationalLocalFactor_eq_of_inertia_ncard
      K23plus s ⟨q, hq⟩ 11 1 hinertia h22.2
    exact Or.inr (Or.inr (Or.inr ⟨h22.1, by simpa using hlocal⟩))

/-- Away from `23`, the full-field local factor is the real-subfield local
factor times the product of the eleven odd-character local factors. -/
theorem unramified_dedekind_local_factorization
    (s : ℂ) {q : ℕ} (hq : Nat.Prime q) (hq23 : q ≠ 23) :
    dedekindRationalLocalFactor K23 s ⟨q, hq⟩ =
      dedekindRationalLocalFactor K23plus s ⟨q, hq⟩ *
        oddCharacterLocalFactorX (q : ZMod 23) ((q : ℂ) ^ (-s)) := by
  have hfull :=
    cyclotomic_dedekindRationalLocalFactor_prime_order_cases s hq hq23
  have hreal :=
    real_dedekindRationalLocalFactor_prime_order_cases s hq hq23
  have heval :=
    evaluated_localFactor_prime_order_cases hq hq23 ((q : ℂ) ^ (-s))
  rcases heval with e1 | e2 | e11 | e22
  · have hf : dedekindRationalLocalFactor K23 s ⟨q, hq⟩ =
        ((1 - (q : ℂ) ^ (-s)) ^ 22)⁻¹ := by
      rcases hfull with f1 | f2 | f11 | f22
      · exact f1.2
      all_goals omega
    have hr : dedekindRationalLocalFactor K23plus s ⟨q, hq⟩ =
        ((1 - (q : ℂ) ^ (-s)) ^ 11)⁻¹ := by
      rcases hreal with r1 | r2 | r11 | r22
      · exact r1.2
      all_goals omega
    rw [hf, hr]
    exact e1.2
  · have hf : dedekindRationalLocalFactor K23 s ⟨q, hq⟩ =
        ((1 - ((q : ℂ) ^ (-s)) ^ 2) ^ 11)⁻¹ := by
      rcases hfull with f1 | f2 | f11 | f22
      · omega
      · exact f2.2
      all_goals omega
    have hr : dedekindRationalLocalFactor K23plus s ⟨q, hq⟩ =
        ((1 - (q : ℂ) ^ (-s)) ^ 11)⁻¹ := by
      rcases hreal with r1 | r2 | r11 | r22
      · omega
      · exact r2.2
      all_goals omega
    rw [hf, hr]
    exact e2.2
  · have hf : dedekindRationalLocalFactor K23 s ⟨q, hq⟩ =
        ((1 - ((q : ℂ) ^ (-s)) ^ 11) ^ 2)⁻¹ := by
      rcases hfull with f1 | f2 | f11 | f22
      · omega
      · omega
      · exact f11.2
      · omega
    have hr : dedekindRationalLocalFactor K23plus s ⟨q, hq⟩ =
        (1 - ((q : ℂ) ^ (-s)) ^ 11)⁻¹ := by
      rcases hreal with r1 | r2 | r11 | r22
      · omega
      · omega
      · exact r11.2
      · omega
    rw [hf, hr]
    exact e11.2
  · have hf : dedekindRationalLocalFactor K23 s ⟨q, hq⟩ =
        (1 - ((q : ℂ) ^ (-s)) ^ 22)⁻¹ := by
      rcases hfull with f1 | f2 | f11 | f22
      all_goals try omega
      exact f22.2
    have hr : dedekindRationalLocalFactor K23plus s ⟨q, hq⟩ =
        (1 - ((q : ℂ) ^ (-s)) ^ 11)⁻¹ := by
      rcases hreal with r1 | r2 | r11 | r22
      all_goals try omega
      exact r22.2
    rw [hf, hr]
    exact e22.2

/-! ## The ramified prime -/

/-- There is one prime above `23` in the maximal real subfield. -/
theorem realSubfield_ncard_primesOver_twentyThree :
    (Ideal.primesOver (Ideal.span {(23 : ℤ)})
      (NumberField.RingOfIntegers K23plus)).ncard = 1 := by
  let p : Ideal ℤ := Ideal.span {(23 : ℤ)}
  letI : p.IsPrime := by
    change (Ideal.span {(23 : ℤ)}).IsPrime
    rw [Ideal.span_singleton_prime]
    · norm_num
    · norm_num
  obtain ⟨P⟩ := (inferInstance : Nonempty
    (Ideal.primesOver p (NumberField.RingOfIntegers K23plus)))
  letI : (P : Ideal (NumberField.RingOfIntegers K23plus)).IsPrime :=
    P.property.1
  letI : (P : Ideal (NumberField.RingOfIntegers K23plus)).LiesOver p :=
    P.property.2
  have htower := Ideal.ncard_primesOver_mul_ncard_primesOver
    (A := ℤ)
    (B := NumberField.RingOfIntegers K23plus)
    (p := p)
    (P : Ideal (NumberField.RingOfIntegers K23plus)) Gal(K23plus/ℚ)
    (C := NumberField.RingOfIntegers K23)
    Gal(K23/ℚ)
  have hfull : (Ideal.primesOver p
      (NumberField.RingOfIntegers K23)).ncard = 1 := by
    simpa [p] using
      (IsCyclotomicExtension.Rat.ncard_primesOver_of_prime 23 K23)
  rw [hfull] at htower
  have hreal : (Ideal.primesOver p
      (NumberField.RingOfIntegers K23plus)).ncard = 1 := by
    apply Nat.eq_one_of_dvd_one
    exact ⟨(Ideal.primesOver (P : Ideal
      (NumberField.RingOfIntegers K23plus))
      (NumberField.RingOfIntegers K23)).ncard, htower.symm⟩
  simpa [p] using hreal

/-- Every real-subfield prime above `23` has residue degree one. -/
theorem realSubfield_inertiaDeg_twentyThree_eq_one
    (P : Ideal.primesOver (Ideal.span {(23 : ℤ)})
      (NumberField.RingOfIntegers K23plus)) :
    (P : Ideal (NumberField.RingOfIntegers K23plus)).inertiaDeg ℤ = 1 := by
  let p : Ideal ℤ := Ideal.span {(23 : ℤ)}
  let P' : Ideal (NumberField.RingOfIntegers K23plus) := P
  have hpne : p ≠ ⊥ := by
    change Ideal.span {(23 : ℤ)} ≠ ⊥
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num
  have hPprime : P'.IsPrime := P.property.1
  have hPne : P' ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hpne P.property
  letI : p.IsPrime := by
    change (Ideal.span {(23 : ℤ)}).IsPrime
    rw [Ideal.span_singleton_prime]
    · norm_num
    · norm_num
  letI : P'.IsPrime := hPprime
  letI : P'.IsMaximal := hPprime.isMaximal hPne
  have hPover : P'.LiesOver p := by simpa [p, P'] using P.property.2
  letI : P'.LiesOver p := hPover
  obtain ⟨Q, hQmax, hQoverP⟩ :=
    exists_maximal_ideal_liesOver_of_isIntegral
      (S := NumberField.RingOfIntegers K23) P'
  letI : Q.IsMaximal := hQmax
  letI : Q.LiesOver P' := hQoverP
  have hQoverZ : Q.LiesOver p := LiesOver.trans Q P' p
  letI : Q.LiesOver p := hQoverZ
  have hfull : Q.inertiaDeg ℤ = 1 := by
    simpa [p] using
      (IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime 23 K23 Q)
  have hdvd : P'.inertiaDeg ℤ ∣ Q.inertiaDeg ℤ :=
    P'.inertiaDeg_below_dvd Q
  rw [hfull] at hdvd
  have hPone : P'.inertiaDeg ℤ = 1 := Nat.eq_one_of_dvd_one hdvd
  simpa [P'] using hPone

/-- All odd-character local factors at the ramified prime are one. -/
theorem oddCharacterLocalFactorX_twentyThree (X : ℂ) :
    oddCharacterLocalFactorX (23 : ZMod 23) X = 1 := by
  classical
  have hzero : (23 : ZMod 23) = 0 := ZMod.natCast_self 23
  rw [oddCharacterLocalFactorX, hzero]
  apply Finset.prod_eq_one
  intro χ hχ
  have hχ0 : χ (0 : ZMod 23) = 0 :=
    MulChar.map_nonunit χ not_isUnit_zero
  rw [hχ0]
  simp

/-- At `23`, the full and real Dedekind factors agree and the odd-character
factor is one. -/
theorem ramified_dedekind_local_factorization (s : ℂ) :
    dedekindRationalLocalFactor K23 s ⟨23, by decide⟩ =
      dedekindRationalLocalFactor K23plus s ⟨23, by decide⟩ *
        oddCharacterLocalFactorX (23 : ZMod 23) ((23 : ℂ) ^ (-s)) := by
  have hfullN : (Ideal.primesOver (Ideal.span {(23 : ℤ)})
      (NumberField.RingOfIntegers K23)).ncard = 1 := by
    simpa using (IsCyclotomicExtension.Rat.ncard_primesOver_of_prime 23 K23)
  have hfullF : ∀ P : Ideal.primesOver (Ideal.span {(23 : ℤ)})
      (NumberField.RingOfIntegers K23),
      (P : Ideal (NumberField.RingOfIntegers K23)).inertiaDeg ℤ = 1 := by
    intro P
    letI : (P : Ideal (NumberField.RingOfIntegers K23)).IsPrime := P.property.1
    letI : (P : Ideal (NumberField.RingOfIntegers K23)).LiesOver
        (Ideal.span {(23 : ℤ)}) := P.property.2
    exact IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime 23 K23 P
  have hfull := dedekindRationalLocalFactor_eq_of_inertia_ncard
    K23 s ⟨23, by decide⟩ 1 1 hfullF hfullN
  have hreal := dedekindRationalLocalFactor_eq_of_inertia_ncard
    K23plus s ⟨23, by decide⟩ 1 1
      realSubfield_inertiaDeg_twentyThree_eq_one
      realSubfield_ncard_primesOver_twentyThree
  rw [hfull, hreal, oddCharacterLocalFactorX_twentyThree]
  simp

end

end BealRegular.TwentyThreeDedekindLocalFactors
