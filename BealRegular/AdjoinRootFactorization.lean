import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.RingTheory.IsAdjoinRoot

/-!
# Factorization from adjoin-root algebra equivalences

This module recovers polynomial irreducibility and two-factor decompositions
from the corresponding quotient-algebra structure.

If `AdjoinRoot f` is a field, then a monic `f` is irreducible.  More generally,
if `AdjoinRoot f` is equivalent to a product of two finite-dimensional fields,
the minimal polynomials of the two projected root coordinates are irreducible.
Their product vanishes in both field coordinates, so it is divisible by `f`;
comparison of dimensions then proves that their product is exactly `f` and
that their degrees equal the dimensions of the two field factors.
-/

namespace BealRegular.AdjoinRootFactorization

open Polynomial

noncomputable section

/-- A monic polynomial is irreducible when its adjoin-root algebra is a
field. -/
theorem irreducible_of_adjoinRoot_isField
    {K : Type*} [Field K] {f : K[X]}
    (hf : f.Monic) (hfield : IsField (AdjoinRoot f)) :
    Irreducible f := by
  have hmax : (Ideal.span {f} : Ideal K[X]).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ hfield
  exact ((Ideal.span_singleton_prime hf.ne_zero).mp hmax.isPrime).irreducible

/-- A field-valued algebra equivalence from an adjoin-root algebra certifies
irreducibility of its monic defining polynomial. -/
theorem irreducible_of_adjoinRoot_algEquiv_isField
    {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    {f : K[X]} (hf : f.Monic) (hL : IsField L)
    (e : AdjoinRoot f ≃ₐ[K] L) :
    Irreducible f := by
  apply irreducible_of_adjoinRoot_isField hf
  exact e.toRingEquiv.toMulEquiv.isField hL

/-- If the adjoin-root algebra of a monic polynomial is a product of two
finite-dimensional fields, the polynomial is exactly a
product of two monic irreducibles having those degrees. -/
theorem exists_two_irreducible_factors_of_adjoinRoot_algEquiv_prod
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    {f : K[X]} (hf : f.Monic)
    (e : AdjoinRoot f ≃ₐ[K] L × M) :
    ∃ g h : K[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
      Irreducible g ∧ Irreducible h ∧
      g.natDegree = Module.finrank K L ∧
      h.natDegree = Module.finrank K M := by
  let projL : AdjoinRoot f →ₐ[K] L :=
    (AlgHom.fst K L M).comp e.toAlgHom
  let projM : AdjoinRoot f →ₐ[K] M :=
    (AlgHom.snd K L M).comp e.toAlgHom
  let alphaL : L := projL (AdjoinRoot.root f)
  let alphaM : M := projM (AdjoinRoot.root f)
  have hintL : IsIntegral K alphaL :=
    (AdjoinRoot.isIntegral_root hf.ne_zero).map projL
  have hintM : IsIntegral K alphaM :=
    (AdjoinRoot.isIntegral_root hf.ne_zero).map projM
  let g : K[X] := minpoly K alphaL
  let h : K[X] := minpoly K alphaM
  have hgmonic : g.Monic := minpoly.monic hintL
  have hhmonic : h.Monic := minpoly.monic hintM
  have hgirr : Irreducible g := minpoly.irreducible hintL
  have hhirr : Irreducible h := minpoly.irreducible hintM
  have hmk : AdjoinRoot.mk f (g * h) = 0 := by
    apply e.injective
    rw [map_zero]
    apply Prod.ext
    · change projL (AdjoinRoot.mk f (g * h)) = 0
      rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply]
      simp [alphaL, g, minpoly.aeval]
    · change projM (AdjoinRoot.mk f (g * h)) = 0
      rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply]
      simp [alphaM, h, minpoly.aeval]
  have hdiv : f ∣ g * h := AdjoinRoot.mk_eq_zero.mp hmk
  have hgdeg_le : g.natDegree ≤ Module.finrank K L :=
    minpoly.natDegree_le alphaL
  have hhdeg_le : h.natDegree ≤ Module.finrank K M :=
    minpoly.natDegree_le alphaM
  letI : Module.Finite K (AdjoinRoot f) := hf.finite_adjoinRoot
  have hdim : f.natDegree =
      Module.finrank K L + Module.finrank K M := by
    have heq := e.toLinearEquiv.finrank_eq
    calc
      f.natDegree = Module.finrank K (AdjoinRoot f) :=
        (AdjoinRoot.isAdjoinRootMonic f hf).finrank.symm
      _ = Module.finrank K (L × M) := heq
      _ = Module.finrank K L + Module.finrank K M := Module.finrank_prod
  have hproddeg_le : (g * h).natDegree ≤ f.natDegree := by
    rw [hgmonic.natDegree_mul hhmonic, hdim]
    exact Nat.add_le_add hgdeg_le hhdeg_le
  have heq : g * h = f :=
    eq_of_monic_of_dvd_of_natDegree_le hf (hgmonic.mul hhmonic)
      hdiv hproddeg_le
  have hsum : g.natDegree + h.natDegree =
      Module.finrank K L + Module.finrank K M := by
    rw [← hgmonic.natDegree_mul hhmonic, heq, hdim]
  have hgdeg : g.natDegree = Module.finrank K L := by omega
  have hhdeg : h.natDegree = Module.finrank K M := by omega
  exact ⟨g, h, hgmonic, hhmonic, heq.symm, hgirr, hhirr, hgdeg, hhdeg⟩

/-- An equivalence to the adjoin-root algebra of an irreducible polynomial
certifies irreducibility of the source defining polynomial. -/
theorem irreducible_of_adjoinRoot_algEquiv_adjoinRoot
    {K : Type*} [Field K] {f g : K[X]}
    (hf : f.Monic) (hg : Irreducible g)
    (e : AdjoinRoot f ≃ₐ[K] AdjoinRoot g) :
    Irreducible f := by
  letI : Fact (Irreducible g) := ⟨hg⟩
  exact irreducible_of_adjoinRoot_algEquiv_isField
    hf (Field.toIsField (AdjoinRoot g)) e

/-- An equivalence to a product of two irreducible adjoin-root algebras
recovers two irreducible factors whose degrees are the degrees of the target
polynomials. -/
theorem exists_two_irreducible_factors_of_adjoinRoot_algEquiv_adjoinRoots
    {K : Type*} [Field K] {f g h : K[X]}
    (hf : f.Monic) (hg : Irreducible g) (hh : Irreducible h)
    (e : AdjoinRoot f ≃ₐ[K] AdjoinRoot g × AdjoinRoot h) :
    ∃ a b : K[X], a.Monic ∧ b.Monic ∧ f = a * b ∧
      Irreducible a ∧ Irreducible b ∧
      a.natDegree = g.natDegree ∧ b.natDegree = h.natDegree := by
  letI : Fact (Irreducible g) := ⟨hg⟩
  letI : Fact (Irreducible h) := ⟨hh⟩
  letI : Module.Finite K (AdjoinRoot g) :=
    (AdjoinRoot.powerBasis hg.ne_zero).finite
  letI : Module.Finite K (AdjoinRoot h) :=
    (AdjoinRoot.powerBasis hh.ne_zero).finite
  obtain ⟨a, b, ha, hb, hab, hai, hbi, hadeg, hbdeg⟩ :=
    exists_two_irreducible_factors_of_adjoinRoot_algEquiv_prod hf e
  refine ⟨a, b, ha, hb, hab, hai, hbi, ?_, ?_⟩
  · rw [hadeg]
    exact (AdjoinRoot.powerBasis hg.ne_zero).finrank.trans
      (AdjoinRoot.powerBasis_dim hg.ne_zero)
  · rw [hbdeg]
    exact (AdjoinRoot.powerBasis hh.ne_zero).finrank.trans
      (AdjoinRoot.powerBasis_dim hh.ne_zero)

end

end BealRegular.AdjoinRootFactorization
