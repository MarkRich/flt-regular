import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Over

/-!
# Residual quotients of adjoin-root algebras

This module packages the compatibility of `AdjoinRoot` with reduction modulo
an ideal.  Quotienting `AdjoinRoot f` by the extended ideal gives the
adjoin-root algebra of the coefficientwise reduction of `f`.  The equivalence
is exposed both over the original coefficient ring and over the residue ring,
with variants for equal or associated residual polynomials and for replacing
the residue ring by an isomorphic ring.

For the signature `(3,5,7)` program, these equivalences provide the residual
input for the complete formally-etale rigidity theorem.  This module does not
prove that any signature-specific lifted factor is formally etale, verify a
particular residual polynomial identity, apply adic rigidity, identify a
Dahmen--Siksek model algebra, rescale a non-etale small factor, classify
ramification, exclude signature `(3,5,7)`, or prove Beal's conjecture.
-/

namespace BealRegular.AdjoinRootReduction

open Polynomial

noncomputable section

universe u v

variable {R : Type u} [CommRing R]

/-- Reducing an adjoin-root algebra modulo an extended ideal commutes with
reducing its defining polynomial, as an algebra equivalence over the original
coefficient ring. -/
def quotientAdjoinRootAlgEquiv (I : Ideal R) (f : R[X]) :
    (AdjoinRoot f ⧸ I.map (AdjoinRoot.of f)) ≃ₐ[R]
      AdjoinRoot (f.map (Ideal.Quotient.mk I)) := by
  change (AdjoinRoot f ⧸ I.map (AdjoinRoot.of f)) ≃ₐ[R]
    ((R ⧸ I)[X] ⧸ Ideal.span ({f.map (Ideal.Quotient.mk I)} : Set (R ⧸ I)[X]))
  exact AdjoinRoot.quotEquivQuotMap f I

/-- The residual equivalence sends the class of the original root to the root
of the reduced polynomial. -/
@[simp]
theorem quotientAdjoinRootAlgEquiv_root (I : Ideal R) (f : R[X]) :
    quotientAdjoinRootAlgEquiv I f
        (Ideal.Quotient.mk (I.map (AdjoinRoot.of f)) (AdjoinRoot.root f)) =
      AdjoinRoot.root (f.map (Ideal.Quotient.mk I)) := by
  change
    AdjoinRoot.quotEquivQuotMap f I
        (Ideal.Quotient.mk (I.map (AdjoinRoot.of f)) (AdjoinRoot.mk f Polynomial.X)) =
      Ideal.Quotient.mk
        (Ideal.span ({f.map (Ideal.Quotient.mk I)} : Set (R ⧸ I)[X])) Polynomial.X
  simpa only [Polynomial.map_X] using
    AdjoinRoot.quotEquivQuotMap_apply_mk f Polynomial.X I

/-- Rewrite the residual defining polynomial by an equality. -/
def quotientAdjoinRootAlgEquivOfEq
    (I : Ideal R) (f : R[X]) (g : (R ⧸ I)[X])
    (h : f.map (Ideal.Quotient.mk I) = g) :
    (AdjoinRoot f ⧸ I.map (AdjoinRoot.of f)) ≃ₐ[R]
      AdjoinRoot g :=
  (quotientAdjoinRootAlgEquiv I f).trans
    ((AdjoinRoot.algEquivOfEq (R ⧸ I) _ g h).restrictScalars R)

/-- Rewrite the residual defining polynomial up to multiplication by a unit. -/
def quotientAdjoinRootAlgEquivOfAssociated
    (I : Ideal R) (f : R[X]) (g : (R ⧸ I)[X])
    (h : Associated (f.map (Ideal.Quotient.mk I)) g) :
    (AdjoinRoot f ⧸ I.map (AdjoinRoot.of f)) ≃ₐ[R]
      AdjoinRoot g :=
  (quotientAdjoinRootAlgEquiv I f).trans
    ((AdjoinRoot.algEquivOfAssociated (R ⧸ I) _ g h).restrictScalars R)

/-- The same reduction, retaining its natural algebra structure over the
residue ring. -/
def quotientAdjoinRootResidueAlgEquiv (I : Ideal R) (f : R[X]) :
    (AdjoinRoot f ⧸ I.map (algebraMap R (AdjoinRoot f))) ≃ₐ[R ⧸ I]
      AdjoinRoot (f.map (Ideal.Quotient.mk I)) := by
  let e :
      (AdjoinRoot f ⧸ I.map (algebraMap R (AdjoinRoot f))) ≃+*
        AdjoinRoot (f.map (Ideal.Quotient.mk I)) := by
    change (AdjoinRoot f ⧸ I.map (AdjoinRoot.of f)) ≃+*
      ((R ⧸ I)[X] ⧸ Ideal.span ({f.map (Ideal.Quotient.mk I)} : Set (R ⧸ I)[X]))
    exact AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot I f
  exact AlgEquiv.ofRingEquiv (f := e) (by
    rintro ⟨x⟩
    change e (Ideal.Quotient.mk _ (AdjoinRoot.of f x)) =
      Ideal.Quotient.mk
        (Ideal.span ({f.map (Ideal.Quotient.mk I)} : Set (R ⧸ I)[X]))
        (Polynomial.C (Ideal.Quotient.mk I x))
    dsimp [e]
    change
      AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot I f
          (Ideal.Quotient.mk (I.map (AdjoinRoot.of f)) (AdjoinRoot.of f x)) =
        Ideal.Quotient.mk
          (Ideal.span ({f.map (Ideal.Quotient.mk I)} : Set (R ⧸ I)[X]))
          (Polynomial.C (Ideal.Quotient.mk I x))
    simpa only [AdjoinRoot.of, RingHom.comp_apply, Polynomial.map_C] using
      AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of I f (Polynomial.C x))

/-- Residual polynomial equality, with the equivalence retaining its natural
`R ⧸ I`-algebra structure. -/
def quotientAdjoinRootResidueAlgEquivOfEq
    (I : Ideal R) (f : R[X]) (g : (R ⧸ I)[X])
    (h : f.map (Ideal.Quotient.mk I) = g) :
    (AdjoinRoot f ⧸ I.map (algebraMap R (AdjoinRoot f))) ≃ₐ[R ⧸ I]
      AdjoinRoot g :=
  (quotientAdjoinRootResidueAlgEquiv I f).trans
    (AdjoinRoot.algEquivOfEq (R ⧸ I) _ g h)

/-- Associated residual polynomials define equivalent residue algebras. -/
def quotientAdjoinRootResidueAlgEquivOfAssociated
    (I : Ideal R) (f : R[X]) (g : (R ⧸ I)[X])
    (h : Associated (f.map (Ideal.Quotient.mk I)) g) :
    (AdjoinRoot f ⧸ I.map (algebraMap R (AdjoinRoot f))) ≃ₐ[R ⧸ I]
      AdjoinRoot g :=
  (quotientAdjoinRootResidueAlgEquiv I f).trans
    (AdjoinRoot.algEquivOfAssociated (R ⧸ I) _ g h)

/-- Replacing the coefficient residue ring by an isomorphic ring and the
residual polynomial by an associated one preserves the quotient ring. -/
def quotientAdjoinRootRingEquivOfMapAssociated
    {K : Type v} [CommRing K]
    (I : Ideal R) (f : R[X]) (e : (R ⧸ I) ≃+* K) (g : K[X])
    (h : Associated ((f.map (Ideal.Quotient.mk I)).map e) g) :
    (AdjoinRoot f ⧸ I.map (algebraMap R (AdjoinRoot f))) ≃+*
      AdjoinRoot g :=
  (quotientAdjoinRootResidueAlgEquiv I f).toRingEquiv.trans
    (AdjoinRoot.mapRingEquiv e _ g h)

end

end BealRegular.AdjoinRootReduction
