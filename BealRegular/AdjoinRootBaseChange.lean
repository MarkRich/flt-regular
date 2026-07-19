import Mathlib.RingTheory.AdjoinRoot

/-!
# Scalar extension of adjoin-root algebras

This module identifies scalar extension of an adjoin-root algebra with the
adjoin-root algebra of the coefficientwise mapped polynomial.  It also
transports algebra equivalences between adjoin-root algebras through scalar
extension and records the exact effect on the canonical base-ring map and root.

The transported equivalence need not send root to root: its root image is the
scalar extension of the image of the original root.  No flatness, finiteness,
separability, or field hypothesis is required.
-/

namespace BealRegular.AdjoinRootBaseChange

open Polynomial
open scoped TensorProduct

noncomputable section

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Adjoining a root commutes with scalar extension. -/
def adjoinRootBaseChangeAlgEquiv (f : R[X]) :
    (S ⊗[R] AdjoinRoot f) ≃ₐ[S]
      AdjoinRoot (f.map (algebraMap R S)) := by
  let q : (S ⊗[R] R)[X] :=
    f.map Algebra.TensorProduct.includeRight.toRingHom
  let e : (S ⊗[R] R) ≃ₐ[S] S := Algebra.TensorProduct.rid R S S
  have he : q.map e.toRingHom = f.map (algebraMap R S) := by
    change (f.map Algebra.TensorProduct.includeRight.toRingHom).map
      e.toRingHom = f.map (algebraMap R S)
    rw [Polynomial.map_map]
    congr 1
    ext r
    simp [e, Algebra.smul_def]
  exact (AdjoinRoot.tensorAlgEquiv f q rfl).trans
    (AdjoinRoot.mapAlgEquiv e q (f.map (algebraMap R S)) (he ▸ .refl _))

/-- The scalar-extension equivalence sends the tensor of the original root to
the root of the coefficientwise mapped polynomial. -/
@[simp]
theorem adjoinRootBaseChangeAlgEquiv_root (f : R[X]) :
    adjoinRootBaseChangeAlgEquiv (S := S) f
        (1 ⊗ₜ AdjoinRoot.root f) =
      AdjoinRoot.root (f.map (algebraMap R S)) := by
  simp only [adjoinRootBaseChangeAlgEquiv, AlgEquiv.trans_apply,
    AdjoinRoot.tensorAlgEquiv_root, AdjoinRoot.coe_mapAlgEquiv,
    AdjoinRoot.map_root]

/-- Compatibility of scalar extension with the canonical map from the
original adjoin-root algebra. -/
theorem adjoinRootBaseChangeAlgEquiv_one_tmul (f : R[X])
    (x : AdjoinRoot f) :
    adjoinRootBaseChangeAlgEquiv (S := S) f (1 ⊗ₜ x) =
      AdjoinRoot.map (algebraMap R S) f (f.map (algebraMap R S))
        (dvd_refl _) x := by
  let lhs : AdjoinRoot f →ₐ[R]
      AdjoinRoot (f.map (algebraMap R S)) :=
    ((adjoinRootBaseChangeAlgEquiv (S := S) f).restrictScalars R).toAlgHom.comp
      Algebra.TensorProduct.includeRight
  let rhs : AdjoinRoot f →ₐ[R]
      AdjoinRoot (f.map (algebraMap R S)) :=
    AdjoinRoot.mapAlgHom (Algebra.ofId R S) f
      (f.map (algebraMap R S)) (dvd_refl _)
  change lhs x = rhs x
  rw [show lhs = rhs by
    apply AdjoinRoot.algHom_ext
    simp [lhs, rhs]]

/-- An equivalence of adjoin-root algebras remains an equivalence after scalar
extension. -/
def adjoinRootMapAlgEquivOfAlgEquiv
    {f g : R[X]} (e : AdjoinRoot f ≃ₐ[R] AdjoinRoot g) :
    AdjoinRoot (f.map (algebraMap R S)) ≃ₐ[S]
      AdjoinRoot (g.map (algebraMap R S)) :=
  (adjoinRootBaseChangeAlgEquiv (S := S) f).symm.trans <|
    (Algebra.TensorProduct.congr (.refl : S ≃ₐ[S] S) e).trans <|
      adjoinRootBaseChangeAlgEquiv (S := S) g

/-- The transported equivalence agrees with the original equivalence on the
canonical images of elements from the original adjoin-root algebra. -/
theorem adjoinRootMapAlgEquivOfAlgEquiv_map
    {f g : R[X]} (e : AdjoinRoot f ≃ₐ[R] AdjoinRoot g)
    (x : AdjoinRoot f) :
    adjoinRootMapAlgEquivOfAlgEquiv (S := S) e
        (AdjoinRoot.map (algebraMap R S) f (f.map (algebraMap R S))
          (dvd_refl _) x) =
      AdjoinRoot.map (algebraMap R S) g (g.map (algebraMap R S))
        (dvd_refl _) (e x) := by
  rw [← adjoinRootBaseChangeAlgEquiv_one_tmul (S := S) f x,
    ← adjoinRootBaseChangeAlgEquiv_one_tmul (S := S) g (e x)]
  simp [adjoinRootMapAlgEquivOfAlgEquiv,
    Algebra.TensorProduct.congr_apply]

/-- Exact root-image formula for a transported equivalence.  It sends the
mapped root to the scalar extension of the image of the original root, which
need not be the mapped root of the target polynomial. -/
theorem adjoinRootMapAlgEquivOfAlgEquiv_root
    {f g : R[X]} (e : AdjoinRoot f ≃ₐ[R] AdjoinRoot g) :
    adjoinRootMapAlgEquivOfAlgEquiv (S := S) e
        (AdjoinRoot.root (f.map (algebraMap R S))) =
      adjoinRootBaseChangeAlgEquiv (S := S) g
        (1 ⊗ₜ e (AdjoinRoot.root f)) := by
  have hfroot :
      (adjoinRootBaseChangeAlgEquiv (S := S) f).symm
          (AdjoinRoot.root (f.map (algebraMap R S))) =
        1 ⊗ₜ AdjoinRoot.root f := by
    apply (adjoinRootBaseChangeAlgEquiv (S := S) f).injective
    simp
  simp [adjoinRootMapAlgEquivOfAlgEquiv, hfroot,
    Algebra.TensorProduct.congr_apply]

end

end BealRegular.AdjoinRootBaseChange
