import BealRegular.Signature357GenericLocalPolynomial
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Descent of signature `(3,5,7)` factor shapes

This module isolates the polynomial descent used after a seven-adic
classification.  Scalar extension may split rational factors, but it cannot
merge them.  Consequently a monic degree-seven polynomial whose scalar
extension is irreducible, or has two irreducible factors of degrees `(1,6)`,
`(2,5)`, or `(3,4)`, has the same restricted factor shape over the base field.

The final theorem specializes this statement to the rational Dahmen--Siksek
fiber and `Q_7`.  It is conditional on an actual polynomial factorization over
`Q_7`; an equivalence of quotient algebras alone is not such a factorization.
It also does not yet construct a product decomposition of the global etale
algebra.
-/

namespace BealRegular.Signature357GlobalFactorShape

open Polynomial
open Signature357GenericLocalPolynomial

noncomputable section

variable {K L : Type*} [Field K] [Field L]

/-- The canonical strong normalization on polynomials over the target field. -/
local instance strongNormalizationMonoidL : StrongNormalizationMonoid L :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- If a scalar extension has exactly two monic irreducible factors, then the
original monic polynomial is irreducible or has exactly two irreducible
factors, with the same degree pair up to order. -/
theorem monic_factor_shape_of_map_eq_two_irreducibles
    (F : K →+* L) {f : K[X]} {g h : L[X]}
    (hf : f.Monic) (hfpos : 0 < f.natDegree)
    (hg : g.Monic) (hh : h.Monic)
    (hgi : Irreducible g) (hhi : Irreducible h)
    (hmap : f.map F = g * h) :
    Irreducible f ∨
      ∃ a b : K[X], a.Monic ∧ b.Monic ∧ f = a * b ∧
        Irreducible a ∧ Irreducible b ∧
        ((a.natDegree = g.natDegree ∧ b.natDegree = h.natDegree) ∨
          (a.natDegree = h.natDegree ∧ b.natDegree = g.natDegree)) := by
  by_cases hfi : Irreducible f
  · exact Or.inl hfi
  right
  have hf1 : f ≠ 1 := by
    intro heq
    rw [heq] at hfpos
    simp at hfpos
  have hnot : ¬ ∀ a b : K[X], a.Monic → b.Monic → a * b = f →
      a.natDegree = 0 ∨ b.natDegree = 0 := by
    intro H
    exact hfi ((hf.irreducible_iff_natDegree).2 ⟨hf1, H⟩)
  push Not at hnot
  obtain ⟨a, b, ha, hb, hab, ha0, hb0⟩ := hnot
  have ha_ne : a ≠ 0 := by
    intro haz
    subst a
    simp at ha0
  have hb_ne : b ≠ 0 := by
    intro hbz
    subst b
    simp at hb0
  have hma_ne : a.map F ≠ 0 :=
    (Polynomial.map_ne_zero_iff F.injective).2 ha_ne
  have hmb_ne : b.map F ≠ 0 :=
    (Polynomial.map_ne_zero_iff F.injective).2 hb_ne
  have hma_nonunit : ¬ IsUnit (a.map F) := by
    intro hu
    have hone : a.map F = 1 := (ha.map F).eq_one_of_isUnit hu
    have hdeg := congrArg Polynomial.natDegree hone
    rw [Polynomial.natDegree_map F] at hdeg
    exact ha0 (by simpa using hdeg)
  have hmb_nonunit : ¬ IsUnit (b.map F) := by
    intro hu
    have hone : b.map F = 1 := (hb.map F).eq_one_of_isUnit hu
    have hdeg := congrArg Polynomial.natDegree hone
    rw [Polynomial.natDegree_map F] at hdeg
    exact hb0 (by simpa using hdeg)
  have hmapped : a.map F * b.map F = g * h := by
    rw [← Polynomial.map_mul, hab, hmap]
  have hnf :
      UniqueFactorizationMonoid.normalizedFactors (a.map F) +
          UniqueFactorizationMonoid.normalizedFactors (b.map F) =
        ({g, h} : Multiset L[X]) := by
    calc
      UniqueFactorizationMonoid.normalizedFactors (a.map F) +
          UniqueFactorizationMonoid.normalizedFactors (b.map F) =
          UniqueFactorizationMonoid.normalizedFactors (a.map F * b.map F) :=
        (UniqueFactorizationMonoid.normalizedFactors_mul hma_ne hmb_ne).symm
      _ = UniqueFactorizationMonoid.normalizedFactors (g * h) := by rw [hmapped]
      _ = ({g, h} : Multiset L[X]) := by
        rw [UniqueFactorizationMonoid.normalizedFactors_mul hgi.ne_zero hhi.ne_zero,
          UniqueFactorizationMonoid.normalizedFactors_irreducible hgi,
          UniqueFactorizationMonoid.normalizedFactors_irreducible hhi,
          hg.normalize_eq_self, hh.normalize_eq_self]
        rfl
  have hcard := congrArg Multiset.card hnf
  rw [Multiset.card_add] at hcard
  have hpairCard : ({g, h} : Multiset L[X]).card = 2 := rfl
  rw [hpairCard] at hcard
  have hfacA0 : UniqueFactorizationMonoid.normalizedFactors (a.map F) ≠ 0 := by
    intro hz
    exact hma_nonunit
      ((UniqueFactorizationMonoid.normalizedFactors_eq_zero_iff hma_ne).1 hz)
  have hfacB0 : UniqueFactorizationMonoid.normalizedFactors (b.map F) ≠ 0 := by
    intro hz
    exact hmb_nonunit
      ((UniqueFactorizationMonoid.normalizedFactors_eq_zero_iff hmb_ne).1 hz)
  have hcardApos : 0 <
      (UniqueFactorizationMonoid.normalizedFactors (a.map F)).card :=
    Multiset.card_pos.mpr hfacA0
  have hcardBpos : 0 <
      (UniqueFactorizationMonoid.normalizedFactors (b.map F)).card :=
    Multiset.card_pos.mpr hfacB0
  have hcardA : (UniqueFactorizationMonoid.normalizedFactors (a.map F)).card = 1 := by
    omega
  have hcardB : (UniqueFactorizationMonoid.normalizedFactors (b.map F)).card = 1 := by
    omega
  obtain ⟨ga, hga⟩ := Multiset.card_eq_one.mp hcardA
  obtain ⟨gb, hgb⟩ := Multiset.card_eq_one.mp hcardB
  have hpairs : ({ga, gb} : Multiset L[X]) = {g, h} := by
    rw [hga, hgb] at hnf
    exact hnf
  have hpairCases : (ga = g ∧ gb = h) ∨ (ga = h ∧ gb = g) := by
    rcases Multiset.cons_eq_cons.mp hpairs with hsame | hswap
    · exact Or.inl ⟨hsame.1, Multiset.singleton_inj.mp hsame.2⟩
    · rcases hswap with ⟨_, cs, hcs1, hcs2⟩
      have hcscard : cs.card = 0 := by
        have hc := congrArg Multiset.card hcs1
        simp only [Multiset.card_singleton, Multiset.card_cons] at hc
        omega
      have hcs : cs = 0 := Multiset.card_eq_zero.mp hcscard
      subst cs
      exact Or.inr ⟨
        (Multiset.singleton_inj.mp hcs2).symm,
        Multiset.singleton_inj.mp hcs1⟩
  have hga_mem : ga ∈ UniqueFactorizationMonoid.normalizedFactors (a.map F) := by
    rw [hga]
    simp
  have hgb_mem : gb ∈ UniqueFactorizationMonoid.normalizedFactors (b.map F) := by
    rw [hgb]
    simp
  have hga_irr : Irreducible ga :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor ga hga_mem
  have hgb_irr : Irreducible gb :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor gb hgb_mem
  have hga_assoc : Associated ga (a.map F) := by
    have H := UniqueFactorizationMonoid.prod_normalizedFactors hma_ne
    rw [hga] at H
    simpa using H
  have hgb_assoc : Associated gb (b.map F) := by
    have H := UniqueFactorizationMonoid.prod_normalizedFactors hmb_ne
    rw [hgb] at H
    simpa using H
  have hma_irr : Irreducible (a.map F) := hga_assoc.irreducible hga_irr
  have hmb_irr : Irreducible (b.map F) := hgb_assoc.irreducible hgb_irr
  have ha_irr : Irreducible a :=
    Polynomial.Monic.irreducible_of_irreducible_map F a ha hma_irr
  have hb_irr : Irreducible b :=
    Polynomial.Monic.irreducible_of_irreducible_map F b hb hmb_irr
  have hdegA : a.natDegree = ga.natDegree := by
    rw [← Polynomial.natDegree_map F]
    exact natDegree_eq_of_degree_eq
      (degree_eq_degree_of_associated hga_assoc).symm
  have hdegB : b.natDegree = gb.natDegree := by
    rw [← Polynomial.natDegree_map F]
    exact natDegree_eq_of_degree_eq
      (degree_eq_degree_of_associated hgb_assoc).symm
  refine ⟨a, b, ha, hb, hab.symm, ha_irr, hb_irr, ?_⟩
  rcases hpairCases with hp | hp
  · exact Or.inl ⟨hdegA.trans (congrArg natDegree hp.1),
      hdegB.trans (congrArg natDegree hp.2)⟩
  · exact Or.inr ⟨hdegA.trans (congrArg natDegree hp.1),
      hdegB.trans (congrArg natDegree hp.2)⟩

/-- A monic polynomial with exactly two irreducible factors of specified,
ordered degrees. -/
def HasTwoIrreducibleFactorsOfDegrees (f : K[X]) (m n : ℕ) : Prop :=
  ∃ g h : K[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
    Irreducible g ∧ Irreducible h ∧ g.natDegree = m ∧ h.natDegree = n

/-- The four polynomial factor shapes allowed by the seven-adic analysis in
the signature `(3,5,7)` route. -/
def HasSignature357FactorShape (f : K[X]) : Prop :=
  Irreducible f ∨
    HasTwoIrreducibleFactorsOfDegrees f 1 6 ∨
    HasTwoIrreducibleFactorsOfDegrees f 2 5 ∨
    HasTwoIrreducibleFactorsOfDegrees f 3 4

/-- A specified two-factor shape after scalar extension descends to the same
shape over the base field, unless the base polynomial is irreducible. -/
theorem irreducible_or_hasTwoFactorsOfDegrees_of_map
    (F : K →+* L) {f : K[X]} (hf : f.Monic) (hfpos : 0 < f.natDegree)
    {m n : ℕ}
    (hshape : HasTwoIrreducibleFactorsOfDegrees (f.map F) m n) :
    Irreducible f ∨ HasTwoIrreducibleFactorsOfDegrees f m n := by
  rcases hshape with ⟨g, h, hg, hh, hmap, hgi, hhi, hgdeg, hhdeg⟩
  rcases monic_factor_shape_of_map_eq_two_irreducibles
      F hf hfpos hg hh hgi hhi hmap with hfi | hsplit
  · exact Or.inl hfi
  rcases hsplit with ⟨a, b, ha, hb, hab, hai, hbi, hdeg⟩
  right
  rcases hdeg with hsame | hswap
  · exact ⟨a, b, ha, hb, hab, hai, hbi,
      hsame.1.trans hgdeg, hsame.2.trans hhdeg⟩
  · exact ⟨b, a, hb, ha, by simpa [mul_comm] using hab, hbi, hai,
      hswap.2.trans hgdeg, hswap.1.trans hhdeg⟩

/-- The complete signature `(3,5,7)` factor-shape restriction descends through
every field embedding. -/
theorem hasSignature357FactorShape_of_map
    (F : K →+* L) {f : K[X]} (hf : f.Monic) (hfdeg : f.natDegree = 7)
    (hshape : HasSignature357FactorShape (f.map F)) :
    HasSignature357FactorShape f := by
  have hfpos : 0 < f.natDegree := by omega
  rcases hshape with hfi | h16 | h25 | h34
  · exact Or.inl (Polynomial.Monic.irreducible_of_irreducible_map F f hf hfi)
  · rcases irreducible_or_hasTwoFactorsOfDegrees_of_map F hf hfpos h16 with hfi | h
    · exact Or.inl hfi
    · exact Or.inr (Or.inl h)
  · rcases irreducible_or_hasTwoFactorsOfDegrees_of_map F hf hfpos h25 with hfi | h
    · exact Or.inl hfi
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases irreducible_or_hasTwoFactorsOfDegrees_of_map F hf hfpos h34 with hfi | h
    · exact Or.inl hfi
    · exact Or.inr (Or.inr (Or.inr h))

section SevenAdicSpecialization

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The monic associate of the rational signature `(3,5,7)` fiber. -/
def rationalMonicFiber (u : ℚ) : ℚ[X] :=
  C (15 : ℚ)⁻¹ * fiberK u

theorem rationalMonicFiber_monic (u : ℚ) :
    (rationalMonicFiber u).Monic := by
  rw [Polynomial.Monic, rationalMonicFiber, leadingCoeff_mul]
  have hlc : (fiberK u).leadingCoeff = 15 := by
    rw [leadingCoeff, fiberK_natDegree]
    simp [fiberK, phiK]
  rw [hlc]
  norm_num

theorem rationalMonicFiber_natDegree (u : ℚ) :
    (rationalMonicFiber u).natDegree = 7 := by
  rw [rationalMonicFiber, natDegree_C_mul]
  · exact fiberK_natDegree u
  · norm_num

/-- The monic rational fiber defines the same principal ideal as the canonical
Dahmen--Siksek fiber. -/
theorem rationalMonicFiber_associated_fiberK (u : ℚ) :
    Associated (rationalMonicFiber u) (fiberK u) := by
  apply associated_unit_mul_left
  rw [isUnit_C, isUnit_iff_ne_zero]
  exact inv_ne_zero (by norm_num)

/-- Seven-adic irreducibility alone already forces rational irreducibility. -/
theorem rationalMonicFiber_irreducible_of_sevenAdic
    {u : ℚ}
    (h : Irreducible
      ((rationalMonicFiber u).map (algebraMap ℚ ℚ_[7]))) :
    Irreducible (rationalMonicFiber u) :=
  Polynomial.Monic.irreducible_of_irreducible_map
    (algebraMap ℚ ℚ_[7]) (rationalMonicFiber u)
      (rationalMonicFiber_monic u) h

/-- Once the exceptional seven-adic fiber is proved to have two irreducible
factors, the rational fiber is irreducible or has exactly two irreducible
factors with the same degree pair. -/
theorem rationalMonicFiber_factorShape_of_sevenAdic_factorization
    {u : ℚ} {g h : ℚ_[7][X]}
    (hg : g.Monic) (hh : h.Monic)
    (hgi : Irreducible g) (hhi : Irreducible h)
    (hmap : (rationalMonicFiber u).map (algebraMap ℚ ℚ_[7]) = g * h) :
    Irreducible (rationalMonicFiber u) ∨
      ∃ a b : ℚ[X], a.Monic ∧ b.Monic ∧
        rationalMonicFiber u = a * b ∧
        Irreducible a ∧ Irreducible b ∧
        ((a.natDegree = g.natDegree ∧ b.natDegree = h.natDegree) ∨
          (a.natDegree = h.natDegree ∧ b.natDegree = g.natDegree)) := by
  exact monic_factor_shape_of_map_eq_two_irreducibles
    (algebraMap ℚ ℚ_[7])
    (rationalMonicFiber_monic u)
    (by rw [rationalMonicFiber_natDegree]; norm_num)
    hg hh hgi hhi hmap

/-- A seven-adic classification with one of the four allowed shapes gives the
same restricted factor shape for the rational monic fiber. -/
theorem rationalMonicFiber_hasFactorShape_of_sevenAdic
    {u : ℚ}
    (hshape : HasSignature357FactorShape
      ((rationalMonicFiber u).map (algebraMap ℚ ℚ_[7]))) :
    HasSignature357FactorShape (rationalMonicFiber u) :=
  hasSignature357FactorShape_of_map
    (algebraMap ℚ ℚ_[7]) (rationalMonicFiber_monic u)
      (rationalMonicFiber_natDegree u) hshape

end SevenAdicSpecialization

end

end BealRegular.Signature357GlobalFactorShape
