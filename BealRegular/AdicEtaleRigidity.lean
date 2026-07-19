import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Etale.Basic

/-!
# Adic rigidity for formally etale algebras

This module develops model-independent infrastructure for formally etale
algebras over complete adic rings, together with a separate finite-module
completeness theorem.  A finite module over a Noetherian adic-complete ring is
complete, and a map from a formally etale algebra into an adic-complete target
is uniquely determined by its reduction.  Consequently, an equivalence
between two residual quotient algebras lifts to an equivalence between the
complete formally etale algebras themselves.

For the signature `(3,5,7)` program, this is the intended rigidity bridge from
equal residual model algebras to exact integral model-algebra identification.
This module does not prove that a particular polynomial quotient is formally
etale, construct any residual quotient equivalence, perform the small-factor
rescaling, identify a Dahmen--Siksek model algebra, classify ramification,
exclude signature `(3,5,7)`, or prove Beal's conjecture.
-/

namespace BealRegular.AdicEtaleRigidity

open TensorProduct

noncomputable section

universe u

/-- A finite module over a Noetherian ring complete for `I` is itself
`I`-adically complete. -/
theorem finiteModule_isAdicComplete_of_noetherian
    {R M : Type u} [CommRing R] {I : Ideal R}
    [AddCommGroup M] [Module R M] [IsNoetherianRing R]
    [Module.Finite R M] [IsAdicComplete I R] :
    IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  let e₁ := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M
  let e₂ := AlgebraTensorModule.congr
    (AdicCompletion.ofAlgEquiv I).symm.toLinearEquiv
    (LinearEquiv.refl R M)
  let e₃ := TensorProduct.lid R M
  let e : AdicCompletion I M ≃ₗ[R] M :=
    (e₁.symm.restrictScalars R).trans (e₂.trans e₃)
  have he (x : M) : e (AdicCompletion.of I M x) = x := by
    simp [e, e₁, e₂, e₃]
  exact ⟨fun x y h ↦ by
    simpa [he] using congrArg e h,
    fun y ↦ ⟨e y, by
      apply e.injective
      simp [he]⟩⟩

/-- A finite algebra over a Noetherian `I`-adically complete ring is complete
for the extension of `I`. -/
theorem finiteAlgebra_isAdicComplete_map_of_noetherian
    {R A : Type u} [CommRing R] {I : Ideal R}
    [CommRing A] [Algebra R A] [IsNoetherianRing R]
    [Module.Finite R A] [IsAdicComplete I R] :
    IsAdicComplete (I.map (algebraMap R A)) A := by
  rw [IsAdicComplete.map_algebraMap_iff]
  exact finiteModule_isAdicComplete_of_noetherian

universe v w

/-- Adic completeness makes a commutative ring separated for the powers of
its ideal of definition. -/
theorem iInf_pow_eq_bot_of_isAdicComplete
    {B : Type u} [CommRing B] (I : Ideal B) [IsAdicComplete I B] :
    ⨅ n : ℕ, I ^ n = ⊥ := by
  simpa using (IsHausdorff.iInf_pow_smul (I := I) (M := B) inferInstance)

/-- Reduction modulo an ideal is a bijection on algebra maps from a formally
etale algebra into an adically complete target. -/
theorem formallyEtale_reduction_bijective_of_isAdicComplete
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FormallyEtale R A]
    (I : Ideal B) [IsAdicComplete I B] :
    Function.Bijective
      (fun g : A →ₐ[R] B ↦ (Ideal.Quotient.mkₐ R I).comp g) := by
  constructor
  · intro g₁ g₂ h
    apply Algebra.FormallyUnramified.ext_of_iInf
      I
      (iInf_pow_eq_bot_of_isAdicComplete I)
    intro x
    exact AlgHom.congr_fun h x
  · intro f
    exact Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete f

/-- An equivalence between residual quotients lifts uniquely to an equivalence
between adically complete formally etale algebras. -/
def formallyEtaleEquivOfQuotientEquiv
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Algebra.FormallyEtale R A] [Algebra.FormallyEtale R B]
    (I : Ideal A) (J : Ideal B)
    [IsAdicComplete I A] [IsAdicComplete J B]
    (e : (A ⧸ I) ≃ₐ[R] (B ⧸ J)) : A ≃ₐ[R] B := by
  let liftG :=
    (formallyEtale_reduction_bijective_of_isAdicComplete J).2
      (e.toAlgHom.comp (Ideal.Quotient.mkₐ R I))
  let g := Classical.choose liftG
  have hg := Classical.choose_spec liftG
  let liftH :=
    (formallyEtale_reduction_bijective_of_isAdicComplete I).2
      (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R J))
  let h := Classical.choose liftH
  have hh := Classical.choose_spec liftH
  have hg_apply (x : A) :
      Ideal.Quotient.mk J (g x) = e (Ideal.Quotient.mk I x) := by
    simpa [g, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using
      AlgHom.congr_fun hg x
  have hh_apply (x : B) :
      Ideal.Quotient.mk I (h x) = e.symm (Ideal.Quotient.mk J x) := by
    simpa [h, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using
      AlgHom.congr_fun hh x
  have hgh : g.comp h = AlgHom.id R B := by
    apply (formallyEtale_reduction_bijective_of_isAdicComplete J).1
    ext x
    change Ideal.Quotient.mk J (g (h x)) = Ideal.Quotient.mk J x
    rw [hg_apply (h x), hh_apply x]
    simp
  have hhg : h.comp g = AlgHom.id R A := by
    apply (formallyEtale_reduction_bijective_of_isAdicComplete I).1
    ext x
    change Ideal.Quotient.mk I (h (g x)) = Ideal.Quotient.mk I x
    rw [hh_apply (g x), hg_apply x]
    simp
  exact AlgEquiv.ofAlgHom g h hgh hhg

/-- The lifted equivalence reduces to the prescribed equivalence of quotient
algebras. -/
@[simp]
theorem formallyEtaleEquivOfQuotientEquiv_mk
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Algebra.FormallyEtale R A] [Algebra.FormallyEtale R B]
    (I : Ideal A) (J : Ideal B)
    [IsAdicComplete I A] [IsAdicComplete J B]
    (e : (A ⧸ I) ≃ₐ[R] (B ⧸ J)) (x : A) :
    Ideal.Quotient.mk J (formallyEtaleEquivOfQuotientEquiv I J e x) =
      e (Ideal.Quotient.mk I x) := by
  let liftG :=
    (formallyEtale_reduction_bijective_of_isAdicComplete J).2
      (e.toAlgHom.comp (Ideal.Quotient.mkₐ R I))
  have hg := Classical.choose_spec liftG
  change Ideal.Quotient.mk J ((Classical.choose liftG) x) = _
  simpa [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using
    AlgHom.congr_fun hg x

end

end BealRegular.AdicEtaleRigidity
