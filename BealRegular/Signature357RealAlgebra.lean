import BealRegular.AdjoinRootBaseChange
import BealRegular.Signature357RealFiber
import BealRegular.Signature357LocalAlgebra
import Mathlib.Analysis.Polynomial.Factorization
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The real algebra of a nonsingular signature `(3,5,7)` fiber

For a real parameter `u` other than the critical values `0` and `1`, the
degree-seven fiber `phi(X) - u` is separable and has exactly one real root.
Factoring a monic normalization over the reals therefore produces one linear
factor and three irreducible quadratic factors.  The Chinese remainder theorem
and the classification of finite algebraic extensions of `ℝ` then identify its
fiber algebra with `ℝ × ℂ × ℂ × ℂ`.

This proves the archimedean algebra statement in Lemma 4.1(i) of the
signature `(3,5,7)` argument.  It does not constrain the degrees of the global
number-field factors, classify their discriminants, exclude the signature, or
prove Beal's conjecture.
-/

namespace BealRegular.Signature357RealAlgebra

open scoped TensorProduct

open Polynomial

open BealRegular.AdjoinRootBaseChange
open BealRegular.Signature357GenericLocalPolynomial
open BealRegular.Signature357LocalAlgebra
open BealRegular.Signature357RealFiber

noncomputable section

private theorem quadratic_adjoinRoot_complex {q : ℝ[X]}
    (hq : q.IsMonicOfDegree 2) (hirr : Irreducible q) :
    Nonempty (AdjoinRoot q ≃ₐ[ℝ] ℂ) := by
  letI : Fact (Irreducible q) := ⟨hirr⟩
  letI : Module.Finite ℝ (AdjoinRoot q) :=
    (AdjoinRoot.powerBasis hq.ne_zero).finite
  letI : Algebra.IsAlgebraic ℝ (AdjoinRoot q) :=
    Algebra.IsAlgebraic.of_finite ℝ (AdjoinRoot q)
  rcases Real.nonempty_algEquiv_or (AdjoinRoot q) with hreal | hcomplex
  · obtain ⟨e⟩ := hreal
    have hfin : Module.finrank ℝ (AdjoinRoot q) = 2 := by
      change Module.finrank ℝ (ℝ[X] ⧸ Ideal.span {q}) = 2
      rw [finrank_quotient_span_eq_natDegree, hq.natDegree_eq]
    have heq := LinearEquiv.finrank_eq e.toLinearEquiv
    rw [hfin] at heq
    norm_num at heq
  · exact hcomplex

private noncomputable def adjoinRootMulEquivProd {p q : ℝ[X]}
    (hcop : IsCoprime p q) :
    AdjoinRoot (p * q) ≃ₐ[ℝ] AdjoinRoot p × AdjoinRoot q := by
  let I : Ideal ℝ[X] := Ideal.span {p}
  let J : Ideal ℝ[X] := Ideal.span {q}
  have hIJ : IsCoprime I J := by
    exact (Ideal.isCoprime_span_singleton_iff p q).2 hcop
  let e₁ : (ℝ[X] ⧸ Ideal.span {p * q}) ≃ₐ[ℝ] (ℝ[X] ⧸ I * J) :=
    Ideal.quotientEquivAlgOfEq ℝ
      (Ideal.span_singleton_mul_span_singleton p q).symm
  let e₂ : (ℝ[X] ⧸ I * J) ≃ₐ[ℝ]
      (ℝ[X] ⧸ I) × (ℝ[X] ⧸ J) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotientMulEquivQuotientProd I J hIJ)
      (fun _ ↦ rfl)
  exact e₁.trans e₂

private theorem monicQuadratic_irreducible_of_noRoot {q : ℝ[X]}
    (hq : q.IsMonicOfDegree 2) (hroot : ∀ x : ℝ, ¬q.IsRoot x) :
    Irreducible q := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [hq.natDegree_eq]
  · exact hroot

private def realMonicFiber (u : ℝ) : ℝ[X] :=
  C (15 : ℝ)⁻¹ * fiberK u

private theorem realMonicFiber_associated (u : ℝ) :
    Associated (realMonicFiber u) (fiberK u) := by
  apply associated_unit_mul_left
  rw [isUnit_C, isUnit_iff_ne_zero]
  exact inv_ne_zero (by norm_num)

private theorem realMonicFiber_isMonicOfDegree (u : ℝ) :
    (realMonicFiber u).IsMonicOfDegree 7 := by
  have hlc : (fiberK u).leadingCoeff = 15 := by
    rw [leadingCoeff, fiberK_natDegree]
    simp [fiberK, phiK]
  constructor
  · rw [realMonicFiber, natDegree_C_mul (inv_ne_zero (by norm_num))]
    exact fiberK_natDegree u
  · rw [Monic, realMonicFiber, leadingCoeff_mul, hlc]
    norm_num

private theorem real_septic_factor_shape {f : ℝ[X]}
    (hf : f.IsMonicOfDegree 7) :
    ∃ q₁ q₂ q₃ ℓ : ℝ[X],
      q₁.IsMonicOfDegree 2 ∧ q₂.IsMonicOfDegree 2 ∧
      q₃.IsMonicOfDegree 2 ∧ ℓ.IsMonicOfDegree 1 ∧
      f = q₁ * (q₂ * (q₃ * ℓ)) := by
  have hf' : f.IsMonicOfDegree (5 + 2) := by simpa using hf
  obtain ⟨q₁, r₅, hq₁, hr₅, hfac₁⟩ :=
    hf'.eq_isMonicOfDegree_two_mul_isMonicOfDegree
  have hr₅' : r₅.IsMonicOfDegree (3 + 2) := by simpa using hr₅
  obtain ⟨q₂, r₃, hq₂, hr₃, hfac₂⟩ :=
    hr₅'.eq_isMonicOfDegree_two_mul_isMonicOfDegree
  have hr₃' : r₃.IsMonicOfDegree (1 + 2) := by simpa using hr₃
  obtain ⟨q₃, ℓ, hq₃, hℓ, hfac₃⟩ :=
    hr₃'.eq_isMonicOfDegree_two_mul_isMonicOfDegree
  refine ⟨q₁, q₂, q₃, ℓ, hq₁, hq₂, hq₃, hℓ, ?_⟩
  rw [hfac₁, hfac₂, hfac₃]

/-- For every nonsingular real parameter, the signature `(3,5,7)` fiber
algebra has one real factor and three complex factors. -/
theorem fiberReal_nonempty_algEquiv_real_prod_complex (u : ℝ)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    Nonempty (FiberAlgebra u ≃ₐ[ℝ] ℝ × (ℂ × (ℂ × ℂ))) := by
  let f : ℝ[X] := realMonicFiber u
  have hfdeg : f.IsMonicOfDegree 7 := realMonicFiber_isMonicOfDegree u
  obtain ⟨q₁, q₂, q₃, ℓ, hq₁, hq₂, hq₃, hℓ, hfac⟩ :=
    real_septic_factor_shape hfdeg
  have hfront : f = ℓ * (q₁ * (q₂ * q₃)) := by
    rw [hfac]
    ac_rfl
  have hfsep : f.Separable := by
    exact (realMonicFiber_associated u).symm.separable
      (fiberK_separable hu0 hu1)
  have hfsepFront : (ℓ * (q₁ * (q₂ * q₃))).Separable := by
    rw [← hfront]
    exact hfsep
  have hℓrest : IsCoprime ℓ (q₁ * (q₂ * q₃)) :=
    hfsepFront.isCoprime
  have hrestSep : (q₁ * (q₂ * q₃)).Separable :=
    hfsepFront.of_mul_right
  have hq₁rest : IsCoprime q₁ (q₂ * q₃) := hrestSep.isCoprime
  have hq₂q₃ : IsCoprime q₂ q₃ := hrestSep.of_mul_right.isCoprime
  obtain ⟨x, hx, hxuniq⟩ := fiberReal_existsUniqueRoot u
  obtain ⟨r, hℓform⟩ := isMonicOfDegree_one_iff.mp hℓ
  have hℓroot : ℓ.IsRoot (-r) := by
    rw [hℓform]
    simp [IsRoot]
  have factorRoot_eq_unique {q : ℝ[X]} (hqf : q ∣ f) {y : ℝ}
      (hy : q.IsRoot y) : y = x := by
    apply hxuniq
    have hfy : f.IsRoot y := by
      obtain ⟨k, hk⟩ := hqf
      rw [hk]
      exact root_mul_right_of_isRoot k hy
    simpa [f, realMonicFiber, IsRoot] using hfy
  have hℓdvd : ℓ ∣ f := ⟨q₁ * (q₂ * q₃), hfront⟩
  have hroot_eq : -r = x := factorRoot_eq_unique hℓdvd hℓroot
  have noRoot_of_coprime_linear {q : ℝ[X]} (hqf : q ∣ f)
      (hcop : IsCoprime q ℓ) : ∀ y : ℝ, ¬q.IsRoot y := by
    intro y hy
    have hyx : y = x := factorRoot_eq_unique hqf hy
    have hℓy : ℓ.IsRoot y := by
      rw [hyx, ← hroot_eq]
      exact hℓroot
    have hc := hcop.map (evalRingHom y)
    have hc' : IsCoprime (q.eval y) (ℓ.eval y) := by simpa using hc
    rw [IsRoot.def.mp hy, IsRoot.def.mp hℓy] at hc'
    exact not_isCoprime_zero_zero hc'
  have hq₁dvd : q₁ ∣ f := by
    refine ⟨ℓ * (q₂ * q₃), ?_⟩
    rw [hfront]
    ac_rfl
  have hq₂dvd : q₂ ∣ f := by
    refine ⟨ℓ * (q₁ * q₃), ?_⟩
    rw [hfront]
    ac_rfl
  have hq₃dvd : q₃ ∣ f := by
    refine ⟨ℓ * (q₁ * q₂), ?_⟩
    rw [hfront]
    ac_rfl
  have hq₁ℓ : IsCoprime q₁ ℓ := hℓrest.of_mul_right_left.symm
  have hq₂ℓ : IsCoprime q₂ ℓ :=
    hℓrest.of_mul_right_right.of_mul_right_left.symm
  have hq₃ℓ : IsCoprime q₃ ℓ :=
    hℓrest.of_mul_right_right.of_mul_right_right.symm
  have hq₁irr : Irreducible q₁ :=
    monicQuadratic_irreducible_of_noRoot hq₁
      (noRoot_of_coprime_linear hq₁dvd hq₁ℓ)
  have hq₂irr : Irreducible q₂ :=
    monicQuadratic_irreducible_of_noRoot hq₂
      (noRoot_of_coprime_linear hq₂dvd hq₂ℓ)
  have hq₃irr : Irreducible q₃ :=
    monicQuadratic_irreducible_of_noRoot hq₃
      (noRoot_of_coprime_linear hq₃dvd hq₃ℓ)
  obtain ⟨e₁⟩ := quadratic_adjoinRoot_complex hq₁ hq₁irr
  obtain ⟨e₂⟩ := quadratic_adjoinRoot_complex hq₂ hq₂irr
  obtain ⟨e₃⟩ := quadratic_adjoinRoot_complex hq₃ hq₃irr
  have eℓ : AdjoinRoot ℓ ≃ₐ[ℝ] ℝ := by
    rw [hℓform]
    exact (AdjoinRoot.algEquivOfEq ℝ (X + C r) (X - C (-r)) (by simp)).trans
      (quotientSpanXSubCAlgEquiv (-r))
  let eAssoc : FiberAlgebra u ≃ₐ[ℝ] AdjoinRoot f :=
    AdjoinRoot.algEquivOfAssociated ℝ (fiberK u) f
      (realMonicFiber_associated u).symm
  let eFront : AdjoinRoot f ≃ₐ[ℝ]
      AdjoinRoot ℓ × AdjoinRoot (q₁ * (q₂ * q₃)) :=
    (AdjoinRoot.algEquivOfEq ℝ f (ℓ * (q₁ * (q₂ * q₃))) hfront).trans
      (adjoinRootMulEquivProd hℓrest)
  let eSplit₁ :
      (AdjoinRoot ℓ × AdjoinRoot (q₁ * (q₂ * q₃))) ≃ₐ[ℝ]
        AdjoinRoot ℓ × (AdjoinRoot q₁ × AdjoinRoot (q₂ * q₃)) :=
    AlgEquiv.prodCongr (AlgEquiv.refl) (adjoinRootMulEquivProd hq₁rest)
  let eSplit₂ :
      (AdjoinRoot ℓ × (AdjoinRoot q₁ × AdjoinRoot (q₂ * q₃))) ≃ₐ[ℝ]
        AdjoinRoot ℓ × (AdjoinRoot q₁ × (AdjoinRoot q₂ × AdjoinRoot q₃)) :=
    AlgEquiv.prodCongr (AlgEquiv.refl)
      (AlgEquiv.prodCongr (AlgEquiv.refl) (adjoinRootMulEquivProd hq₂q₃))
  exact ⟨eAssoc.trans <| eFront.trans <| eSplit₁.trans <| eSplit₂.trans <|
    AlgEquiv.prodCongr eℓ
      (AlgEquiv.prodCongr e₁ (AlgEquiv.prodCongr e₂ e₃))⟩

/-- The scalar extension to `ℝ` of every noncritical rational
signature `(3,5,7)` fiber has one real factor and three complex factors. -/
theorem fiberRatBaseChangeReal_nonempty_algEquiv_real_prod_complex
    (u : ℚ) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    Nonempty
      ((ℝ ⊗[ℚ] FiberAlgebra u) ≃ₐ[ℝ]
        ℝ × (ℂ × (ℂ × ℂ))) := by
  have hu0' : algebraMap ℚ ℝ u ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℚ ℝ).injective).2 hu0
  have hu1' : algebraMap ℚ ℝ u ≠ 1 := by
    rw [← map_one (algebraMap ℚ ℝ), (algebraMap ℚ ℝ).injective.ne_iff]
    exact hu1
  obtain ⟨e⟩ := fiberReal_nonempty_algEquiv_real_prod_complex
    (algebraMap ℚ ℝ u) hu0' hu1'
  refine ⟨(adjoinRootBaseChangeAlgEquiv (S := ℝ)
    (fiberK (K := ℚ) u)).trans ?_⟩
  rw [fiberK_map]
  exact e

end

end BealRegular.Signature357RealAlgebra
