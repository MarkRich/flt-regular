module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.DFinsupp.Multiset
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Euler products over a free commutative monoid

This file proves the analytic grouping lemma needed for Euler products.  If
`f : alpha -> C` is absolutely summable and every `norm (f a)` is less than
one, then the product of the geometric factors `(1 - f a)^-1` converges to the
sum of the multiplicative weights of all finite multisets of elements of
`alpha`.

The proof first evaluates finite Cartesian products of absolutely convergent
series.  It then decomposes a finitely supported exponent vector into its
finite support and a positive exponent on each support element.  Absolute
summability justifies every regrouping.
-/

@[expose] public section

open scoped BigOperators Topology

noncomputable section

namespace BealRegular.MultisetEulerProduct

universe u v w

/-! ## Finite Cartesian products of series -/

set_option maxHeartbeats 2000000 in
-- The explicit `Fin n` induction creates large dependent equivalence terms.
/-- Absolute summability of a finite product of absolutely summable series. -/
theorem summable_norm_pi_prod
    {ι : Type u} {B : Type v} {R : Type w} [NormedCommRing R] [CompleteSpace R]
    [Fintype ι] (F : ι -> B -> R)
    (hF : forall i, Summable (fun b => norm (F i b))) :
    Summable (fun x : ι -> B => norm (Finset.univ.prod fun i => F i (x i))) := by
  classical
  have hFin : forall n : ℕ, forall F : Fin n -> B -> R,
      (forall i, Summable (fun b => norm (F i b))) ->
      Summable
        (fun x : Fin n -> B => norm (Finset.univ.prod fun i => F i (x i))) := by
    intro n
    induction n with
    | zero =>
        intro F hF
        exact Summable.of_finite
    | succ n ih =>
        intro F hF
        let E : (Fin (n + 1) -> B) ≃ B × (Fin n -> B) := {
          toFun := fun x => ⟨x 0, fun i => x i.succ⟩
          invFun := fun x => Fin.cases x.1 x.2
          left_inv := fun x => by
            funext i
            exact Fin.cases rfl (fun _ => rfl) i
          right_inv := fun x => by
            rcases x with ⟨b, x⟩
            rfl
        }
        have h0 : Summable (fun b => norm (F 0 b)) := hF 0
        have ht : Summable
            (fun x : Fin n -> B =>
              norm (Finset.univ.prod fun i => F i.succ (x i))) :=
          ih (fun i => F i.succ) (fun i => hF i.succ)
        have hp : Summable (fun x : B × (Fin n -> B) =>
            norm (F 0 x.1) *
              norm (Finset.univ.prod fun i => F i.succ (x.2 i))) :=
          Summable.mul_of_nonneg h0 ht
            (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
        have hComp : Summable
            ((fun x : B × (Fin n -> B) =>
              norm (F 0 x.1) *
                norm (Finset.univ.prod fun i => F i.succ (x.2 i))) ∘ E) :=
          E.summable_iff.mpr hp
        exact hComp.of_nonneg_of_le (fun _ => norm_nonneg _) fun x => by
          simp only [Function.comp_apply]
          rw [Fin.prod_univ_succ]
          exact norm_mul_le _ _
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Ffin : Fin (Fintype.card ι) -> B -> R := fun i => F (e.symm i)
  have hfin := hFin (Fintype.card ι) Ffin (fun i => hF (e.symm i))
  let E : (ι -> B) ≃ (Fin (Fintype.card ι) -> B) :=
    Equiv.piCongrLeft (fun _ => B) e
  have hComp : Summable
      ((fun x : Fin (Fintype.card ι) -> B =>
        norm (Finset.univ.prod fun i => Ffin i (x i))) ∘ E) :=
    E.summable_iff.mpr hfin
  have hprod (x : ι -> B) :
      (Finset.univ.prod fun i : ι => F i (x i)) =
        Finset.univ.prod fun i : Fin (Fintype.card ι) => Ffin i (E x i) := by
    exact Fintype.prod_equiv e
      (fun i : ι => F i (x i))
      (fun i : Fin (Fintype.card ι) => Ffin i (E x i))
      (fun i => by simp [E, Ffin])
  exact hComp.congr fun x => congr_arg norm (hprod x).symm

/-- The sum over a finite Cartesian product is the product of the component sums. -/
theorem tsum_pi_prod
    {ι : Type u} {B : Type v} {R : Type w} [NormedCommRing R] [CompleteSpace R]
    [Fintype ι] (F : ι -> B -> R)
    (hF : forall i, Summable (fun b => norm (F i b))) :
    (∑' x : ι -> B, Finset.univ.prod fun i => F i (x i)) =
      Finset.univ.prod fun i => ∑' b, F i b := by
  classical
  refine Fintype.induction_empty_option
    (P := fun (ι : Type u) [Fintype ι] =>
      forall F : ι -> B -> R, (forall i, Summable (fun b => norm (F i b))) ->
        (∑' x : ι -> B, Finset.univ.prod fun i => F i (x i)) =
          Finset.univ.prod fun i => ∑' b, F i b)
      ?_ ?_ ?_ ι F hF
  · intro α β instβ e h F hF
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let E : (α -> B) ≃ (β -> B) := Equiv.piCongrLeft (fun _ => B) e
    have hprod (x : α -> B) :
        (Finset.univ.prod fun i : α => F (e i) (x i)) =
          Finset.univ.prod fun i : β => F i (E x i) := by
      exact Fintype.prod_equiv e
        (fun i : α => F (e i) (x i))
        (fun i : β => F i (E x i))
        (fun i => by simp [E])
    have ih := h (fun i => F (e i)) (fun i => hF (e i))
    calc
      (∑' x : _ -> B, Finset.univ.prod fun i => F i (x i)) =
          ∑' x : α -> B, Finset.univ.prod fun i : β => F i (E x i) :=
            (E.tsum_eq
              (fun x : β -> B => Finset.univ.prod fun i => F i (x i))).symm
      _ = ∑' x : α -> B,
          Finset.univ.prod fun i : α => F (e i) (x i) := by
            apply tsum_congr
            intro x
            exact (hprod x).symm
      _ = Finset.univ.prod fun i : α => ∑' b, F (e i) b := ih
      _ = Finset.univ.prod fun i => ∑' b, F i b := by
            exact Fintype.prod_equiv e (fun i => ∑' b, F (e i) b)
              (fun i => ∑' b, F i b) (fun _ => rfl)
  · intro F _
    simp
  · intro α instα h F hF
    let Ftail : α -> B -> R := fun i => F (some i)
    have h0 : Summable (fun b => norm (F none b)) := hF none
    have ht : Summable
        (fun x : α -> B => norm (Finset.univ.prod fun i => Ftail i (x i))) :=
      summable_norm_pi_prod Ftail (fun i => hF (some i))
    have ih := h Ftail (fun i => hF (some i))
    let E : (Option α -> B) ≃ B × (α -> B) := Equiv.piOptionEquivProd
    calc
      (∑' x : Option α -> B, Finset.univ.prod fun i => F i (x i)) =
          ∑' x : B × (α -> B),
            F none x.1 * Finset.univ.prod fun i => Ftail i (x.2 i) := by
            simpa [E, Ftail, Function.comp_def] using
              (E.symm.tsum_eq
                (fun x : Option α -> B => Finset.univ.prod fun i => F i (x i))).symm
      _ = (∑' b, F none b) *
          ∑' x : α -> B, Finset.univ.prod fun i => Ftail i (x i) := by
            exact (tsum_mul_tsum_of_summable_norm h0 ht).symm
      _ = (∑' b, F none b) * Finset.univ.prod fun i => ∑' b, Ftail i b := by
            rw [ih]
      _ = Finset.univ.prod fun i : Option α => ∑' b, F i b := by
            simp [Ftail, Fintype.prod_option]

/-! ## The free-commutative-monoid Euler product -/

/-- Positive natural numbers, represented in the form used by
`DFinsupp.sigmaFinsetFunEquiv`. -/
abbrev NonzeroNat := {n : ℕ // n ≠ 0}

/-- The nonzero naturals identified with the complement of the singleton
used by `Summable.sum_add_tsum_subtype_compl`. -/
private def nonzeroNatEquivComplSingleton :
    NonzeroNat ≃ {n : ℕ // n ∉ ({0} : Finset ℕ)} :=
  Equiv.subtypeEquivProp (by
    funext n
    simp)

/-- The positive powers at one Euler factor. -/
def positivePower {α : Type*} (f : α -> ℂ) (a : α) (n : NonzeroNat) : ℂ :=
  f a ^ n.1

/-- The positive-degree tail of one geometric series. -/
def positiveTail {α : Type*} (f : α -> ℂ) (a : α) : ℂ :=
  ∑' n : NonzeroNat, positivePower f a n

/-- The sum of the norms in the positive-degree tail. -/
def positiveNormTail {α : Type*} (f : α -> ℂ) (a : α) : ℝ :=
  ∑' n : NonzeroNat, norm (positivePower f a n)

/-- The monomial attached to a finitely supported exponent vector. -/
def exponentWeight {α : Type*} [DecidableEq α] (f : α -> ℂ)
    (d : Π₀ _ : α, ℕ) : ℂ :=
  d.prod (fun a n => f a ^ n)

/-- The multiplicative weight of a finite multiset. -/
def multisetWeight {α : Type*} (f : α -> ℂ)
    (m : Multiset α) : ℂ :=
  letI := Classical.decEq α
  exponentWeight f (Multiset.toDFinsupp m)

theorem multisetWeight_eq_prod_map
    {α : Type*} (f : α -> ℂ) (m : Multiset α) :
    multisetWeight f m = (m.map f).prod := by
  classical
  induction m using Multiset.induction_on with
  | empty => simp [multisetWeight, exponentWeight, DFinsupp.prod]
  | @cons a m ih =>
      have hdf : Multiset.toDFinsupp (a ::ₘ m) =
          DFinsupp.single a 1 + Multiset.toDFinsupp m := by
        rw [show a ::ₘ m = ({a} : Multiset α) + m by rfl, map_add,
          Multiset.toDFinsupp_singleton]
      rw [multisetWeight, hdf, exponentWeight,
        DFinsupp.prod_add_index (fun _ => pow_zero _) (fun _ => pow_add _),
        DFinsupp.prod_single_index (pow_zero _)]
      simpa [multisetWeight, exponentWeight] using
        congr_arg (fun z => f a * z) ih

/-- A support together with a positive exponent at each support element. -/
abbrev SupportAssignment {α : Type*} (s : Finset α) := s -> NonzeroNat

/-- The monomial represented by a support and its positive exponents. -/
def sigmaWeight {α : Type*} (f : α -> ℂ)
    (z : Σ s : Finset α, SupportAssignment s) : ℂ :=
  Finset.univ.prod fun a : z.1 => positivePower f a.1 (z.2 a)

theorem exponentWeight_eq_sigmaWeight
    {α : Type*} [DecidableEq α] (f : α -> ℂ) (d : Π₀ _ : α, ℕ) :
    exponentWeight f d = sigmaWeight f (DFinsupp.sigmaFinsetFunEquiv d) := by
  classical
  simp only [exponentWeight, sigmaWeight, positivePower, DFinsupp.prod,
    DFinsupp.sigmaFinsetFunEquiv_apply_snd_coe]
  exact (Finset.prod_attach d.support (fun a => f a ^ d a)).symm

theorem sigmaWeight_norm_summable
    {α : Type*} (f : α -> ℂ)
    (hlocal : forall a,
      Summable (fun n : NonzeroNat => norm (positivePower f a n)))
    (s : Finset α) :
    Summable (fun k : SupportAssignment s => norm (sigmaWeight f ⟨s, k⟩)) := by
  classical
  simpa [sigmaWeight] using
    (summable_norm_pi_prod (R := ℂ)
      (fun a : s => fun n : NonzeroNat => positivePower f a.1 n)
      (fun a => hlocal a.1))

theorem sigmaWeight_norm_tsum
    {α : Type*} (f : α -> ℂ)
    (hlocal : forall a,
      Summable (fun n : NonzeroNat => norm (positivePower f a n)))
    (s : Finset α) :
    (∑' k : SupportAssignment s, norm (sigmaWeight f ⟨s, k⟩)) =
      ∏ a ∈ s, positiveNormTail f a := by
  classical
  have h := tsum_pi_prod (R := ℝ)
    (fun a : s => fun n : NonzeroNat => norm (positivePower f a.1 n))
    (fun a => by simpa only [norm_norm] using hlocal a.1)
  calc
    (∑' k : SupportAssignment s, norm (sigmaWeight f ⟨s, k⟩)) =
        Finset.univ.prod fun a : s => positiveNormTail f a.1 := by
          simpa only [sigmaWeight, positiveNormTail, norm_prod] using h
    _ = ∏ a ∈ s, positiveNormTail f a :=
      Finset.prod_coe_sort s (positiveNormTail f)

theorem sigmaWeight_tsum
    {α : Type*} (f : α -> ℂ)
    (hlocal : forall a,
      Summable (fun n : NonzeroNat => norm (positivePower f a n)))
    (s : Finset α) :
    (∑' k : SupportAssignment s, sigmaWeight f ⟨s, k⟩) =
      ∏ a ∈ s, positiveTail f a := by
  classical
  have h := tsum_pi_prod (R := ℂ)
    (fun a : s => fun n : NonzeroNat => positivePower f a.1 n)
    (fun a => hlocal a.1)
  calc
    (∑' k : SupportAssignment s, sigmaWeight f ⟨s, k⟩) =
        Finset.univ.prod fun a : s => positiveTail f a.1 := by
          simpa only [sigmaWeight, positiveTail] using h
    _ = ∏ a ∈ s, positiveTail f a :=
      Finset.prod_coe_sort s (positiveTail f)

theorem sigmaWeight_norm_summable_all
    {α : Type*} (f : α -> ℂ)
    (hlocal : forall a,
      Summable (fun n : NonzeroNat => norm (positivePower f a n)))
    (htail : Summable (positiveNormTail f)) :
    Summable (fun z : Σ s : Finset α, SupportAssignment s =>
      norm (sigmaWeight f z)) := by
  classical
  rw [summable_sigma_of_nonneg (fun z => norm_nonneg (sigmaWeight f z))]
  refine ⟨sigmaWeight_norm_summable f hlocal, ?_⟩
  have hout : Summable (fun s : Finset α =>
      ∏ a ∈ s, positiveNormTail f a) :=
    summable_finsetProd_of_summable_norm htail.norm
  exact hout.congr (fun s => (sigmaWeight_norm_tsum f hlocal s).symm)

theorem multisetWeight_norm_summable
    {α : Type*} (f : α -> ℂ)
    (hlocal : forall a,
      Summable (fun n : NonzeroNat => norm (positivePower f a n)))
    (htail : Summable (positiveNormTail f)) :
    Summable (fun m : Multiset α => norm (multisetWeight f m)) := by
  classical
  let E : (Π₀ _ : α, ℕ) ≃
      Σ s : Finset α, SupportAssignment s :=
    DFinsupp.sigmaFinsetFunEquiv
  have hsigma := sigmaWeight_norm_summable_all f hlocal htail
  have hdf : Summable (fun d : Π₀ _ : α, ℕ => norm (exponentWeight f d)) := by
    have hcomp : Summable
        ((fun z => norm (sigmaWeight f z)) ∘ E) :=
      E.summable_iff.mpr hsigma
    exact hcomp.congr fun d => by
      simp [E, exponentWeight_eq_sigmaWeight]
  let M : Multiset α ≃ (Π₀ _ : α, ℕ) :=
    Multiset.equivDFinsupp.toEquiv
  have hcomp : Summable
      ((fun d => norm (exponentWeight f d)) ∘ M) :=
    M.summable_iff.mpr hdf
  exact hcomp.congr fun m => by rfl

theorem positiveTail_one_add
    {α : Type*} (f : α -> ℂ) (a : α) (h : norm (f a) < 1) :
    1 + positiveTail f a = (1 - f a)⁻¹ := by
  have hgeom : Summable (fun n : ℕ => f a ^ n) :=
    summable_geometric_of_norm_lt_one h
  have hsplit := hgeom.sum_add_tsum_subtype_compl ({0} : Finset ℕ)
  have htail : positiveTail f a =
      ∑' n : {n : ℕ // n ∉ ({0} : Finset ℕ)}, f a ^ n.1 := by
    simpa [positiveTail, positivePower, Function.comp_def,
      nonzeroNatEquivComplSingleton, Equiv.subtypeEquivProp,
      Equiv.subtypeEquiv] using
        (nonzeroNatEquivComplSingleton.tsum_eq
          (fun n : {n : ℕ // n ∉ ({0} : Finset ℕ)} => f a ^ n.1))
  rw [← tsum_geometric_of_norm_lt_one h]
  rw [htail]
  simpa using hsplit

theorem positivePower_norm_summable
    {α : Type*} (f : α -> ℂ) (a : α) (h : norm (f a) < 1) :
    Summable (fun n : NonzeroNat => norm (positivePower f a n)) := by
  have hgeom : Summable (fun n : ℕ => f a ^ n) :=
    summable_geometric_of_norm_lt_one h
  have hcompl : Summable
      (fun n : {n : ℕ // n ∉ ({0} : Finset ℕ)} => ‖f a ^ n.1‖) :=
    hgeom.norm.subtype (fun n : ℕ => n ∉ ({0} : Finset ℕ))
  have htransport :=
    nonzeroNatEquivComplSingleton.summable_iff.mpr hcompl
  simpa [Function.comp_def, positivePower, nonzeroNatEquivComplSingleton,
    Equiv.subtypeEquivProp, Equiv.subtypeEquiv] using htransport

theorem positiveNormTail_eq_div
    {α : Type*} (f : α -> ℂ) (a : α) (h : norm (f a) < 1) :
    positiveNormTail f a = norm (f a) / (1 - norm (f a)) := by
  let r : ℝ := norm (f a)
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr : r < 1 := h
  have hrnorm : norm r < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hgeom : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one hrnorm
  have hsplit := hgeom.sum_add_tsum_subtype_compl ({0} : Finset ℕ)
  have htail : positiveNormTail f a =
      ∑' n : {n : ℕ // n ∉ ({0} : Finset ℕ)}, r ^ n.1 := by
    simpa [r, positiveNormTail, positivePower, Function.comp_def,
      nonzeroNatEquivComplSingleton, Equiv.subtypeEquivProp,
      Equiv.subtypeEquiv, norm_pow, Real.norm_eq_abs, abs_of_nonneg hr0] using
        (nonzeroNatEquivComplSingleton.tsum_eq
          (fun n : {n : ℕ // n ∉ ({0} : Finset ℕ)} => r ^ n.1))
  have hone : 1 + positiveNormTail f a = (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_norm_lt_one hrnorm]
    rw [htail]
    simpa using hsplit
  have hne : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr)
  calc
    positiveNormTail f a = (1 - r)⁻¹ - 1 := by linarith
    _ = r / (1 - r) := by
      field_simp [hne]
      ring

theorem positiveNormTail_summable_of_summable_norm
    {α : Type*} (f : α -> ℂ)
    (hsum : Summable (fun a => norm (f a)))
    (hunit : forall a, norm (f a) < 1) :
    Summable (positiveNormTail f) := by
  apply (hsum.mul_left 2).of_norm_bounded_eventually
  filter_upwards
    [hsum.tendsto_cofinite_zero.eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 2)] with a ha
  have hr0 : 0 ≤ norm (f a) := norm_nonneg _
  have hden : 0 < 1 - norm (f a) := sub_pos.mpr (hunit a)
  rw [positiveNormTail_eq_div f a (hunit a), Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr0 hden.le)]
  apply (div_le_iff₀ hden).2
  nlinarith

theorem multisetWeight_tsum_eq_finsetTail_tsum
    {α : Type*} (f : α -> ℂ)
    (hlocal : forall a,
      Summable (fun n : NonzeroNat => norm (positivePower f a n)))
    (htail : Summable (positiveNormTail f)) :
    (∑' m : Multiset α, multisetWeight f m) =
      ∑' s : Finset α, ∏ a ∈ s, positiveTail f a := by
  classical
  let M : Multiset α ≃ (Π₀ _ : α, ℕ) :=
    Multiset.equivDFinsupp.toEquiv
  let E : (Π₀ _ : α, ℕ) ≃
      Σ s : Finset α, SupportAssignment s :=
    DFinsupp.sigmaFinsetFunEquiv
  have hmnorm := multisetWeight_norm_summable f hlocal htail
  have hm : Summable (multisetWeight f) := hmnorm.of_norm
  have hdf : Summable (exponentWeight f) := by
    have hcomp : Summable ((exponentWeight f) ∘ M) := by
      exact hm.congr fun m => by
        rfl
    exact M.summable_iff.mp hcomp
  have hsigma : Summable (sigmaWeight f) := by
    have hcomp : Summable ((sigmaWeight f) ∘ E) := by
      exact hdf.congr fun d => exponentWeight_eq_sigmaWeight f d
    exact E.summable_iff.mp hcomp
  calc
    (∑' m : Multiset α, multisetWeight f m) =
        ∑' m : Multiset α, exponentWeight f (M m) := by
          apply tsum_congr
          intro m
          rfl
    _ = ∑' d : Π₀ _ : α, ℕ, exponentWeight f d :=
      M.tsum_eq (exponentWeight f)
    _ = ∑' d : Π₀ _ : α, ℕ, sigmaWeight f (E d) := by
          apply tsum_congr
          intro d
          exact exponentWeight_eq_sigmaWeight f d
    _ = ∑' z : Σ s : Finset α, SupportAssignment s, sigmaWeight f z :=
      E.tsum_eq (sigmaWeight f)
    _ = ∑' s : Finset α,
        ∑' k : SupportAssignment s, sigmaWeight f ⟨s, k⟩ :=
          hsigma.tsum_sigma
    _ = ∑' s : Finset α, ∏ a ∈ s, positiveTail f a := by
          congr 1
          funext s
          exact sigmaWeight_tsum f hlocal s

/-- The Euler product over generators of a free commutative monoid equals the
sum of the induced multiplicative weights on all finite multisets. -/
theorem hasProd_geometric_eq_tsum_multiset
    {α : Type*} (f : α -> ℂ)
    (hsum : Summable (fun a => norm (f a)))
    (hunit : forall a, norm (f a) < 1) :
    HasProd (fun a => (1 - f a)⁻¹)
      (∑' m : Multiset α, multisetWeight f m) := by
  classical
  have hlocal : forall a,
      Summable (fun n : NonzeroNat => norm (positivePower f a n)) :=
    fun a => positivePower_norm_summable f a (hunit a)
  have htail : Summable (positiveNormTail f) :=
    positiveNormTail_summable_of_summable_norm f hsum hunit
  have htailNorm : Summable (fun a => norm (positiveTail f a)) :=
    htail.of_nonneg_of_le (fun _ => norm_nonneg _) fun a =>
      norm_tsum_le_tsum_norm (hlocal a)
  have hfin : Summable (fun s : Finset α =>
      ∏ a ∈ s, positiveTail f a) :=
    summable_finsetProd_of_summable_norm htailNorm
  have hp : HasProd (fun a => 1 + positiveTail f a)
      (∑' s : Finset α, ∏ a ∈ s, positiveTail f a) :=
    hasProd_one_add_of_hasSum_prod hfin.hasSum
  have hp' : HasProd (fun a => (1 - f a)⁻¹)
      (∑' s : Finset α, ∏ a ∈ s, positiveTail f a) :=
    hp.congr_fun (fun a => (positiveTail_one_add f a (hunit a)).symm)
  rw [multisetWeight_tsum_eq_finsetTail_tsum f hlocal htail]
  exact hp'

end BealRegular.MultisetEulerProduct
