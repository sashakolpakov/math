import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.PrimitiveCover
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportCohomology
import Mathlib.Topology.ShrinkingLemma
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj

/-! # Cech Descent -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.CechDescent

noncomputable section

section

/-! Simultaneous local primitives on the pairwise overlaps of a refined cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.CompactSupportCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X) (n : ℕ)
  (c : ∀ i j, AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) (TopCat.of ↥(U i ⊓ U j)) (n + 1))

structure SingularPairPrimitiveRefinement where
  cover : X × I → Opens X
  subset : ∀ a, cover a ≤ U a.2
  covers : ∀ x, ∃ a, x ∈ cover a
  primitive : ∀ a b,
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of ↥(cover a ⊓ cover b))).X n
  differential : ∀ a b,
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of ↥(cover a ⊓ cover b))).d n (n + 1)
        (primitive a b) =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ)
        ((Opens.toTopCat X).map (homOfLE (inf_le_inf (subset a) (subset b))))).f (n + 1)
          (c a.2 b.2).val

theorem nonempty_singularPairPrimitiveRefinement [Finite I] [NormalSpace X]
    [StronglyLocallyContractibleSpace X] (hc : ∀ x, ∃ i, x ∈ U i) :
    Nonempty (SingularPairPrimitiveRefinement U n c) := by
  classical
  let A := ModuleCat.of ℚ ℚ
  obtain ⟨V, hVc, hVo, hVU⟩ := exists_subset_iUnion_closure_subset
    (s := (Set.univ : Set X)) isClosed_univ (fun i => (U i).isOpen)
    (fun i _ => Set.toFinite {j | i ∈ U j}) (by
      intro x _
      exact Set.mem_iUnion.mpr (hc x))
  let K : I → Set X := fun i => closure (V i)
  have hKU (i : I) : K i ⊆ U i := hVU i
  let H : X → I → I → Prop := fun p i j => p ∈ K i ∩ K j
  have local_exists (p : X) (i j : I) (h : H p i j) :
      ∃ (D : Opens X) (_ : p ∈ D) (hD : D ≤ U i ⊓ U j)
        (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains A (TopCat.of D)).X n),
        (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains A (TopCat.of D)).d n (n + 1) b =
          (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback A ((Opens.toTopCat X).map (homOfLE hD))).f (n + 1) (c i j).val :=
    AlgebraicTopology.Cohomology.Singular.LocalPrimitives.exists_local_singularPrimitive A X (U i ⊓ U j) p ⟨hKU i h.1, hKU j h.2⟩ n (c i j)
  choose L hLp hLU b hb using local_exists
  let D (p : X) (i j : I) : Opens X :=
    if h : H p i j then L p i j h else
      ⟨(K i ∩ K j)ᶜ, (isClosed_closure.inter isClosed_closure).isOpen_compl⟩
  have hD (p : X) (i j : I) : p ∈ D p i j := by
    dsimp [D]
    split_ifs with h
    · exact hLp p i j h
    · exact h
  let O : X → Opens X := fun p => ⨅ ij : I × I, D p ij.1 ij.2
  have hO (p : X) : p ∈ O p := by
    change p ∈ ((⨅ ij : I × I, D p ij.1 ij.2 : Opens X) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr (fun ij => hD p ij.1 ij.2)
  have hOD (p : X) (i j : I) : O p ≤ D p i j := iInf_le _ (i, j)
  let W : X × I → Opens X := fun a => O a.1 ⊓ ⟨V a.2, hVo a.2⟩
  have hWU (a : X × I) : W a ≤ U a.2 := by
    intro x hx
    exact hKU a.2 (subset_closure hx.2)
  have hWc (x : X) : ∃ a, x ∈ W a := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hVc (Set.mem_univ x))
    exact ⟨(x, i), hO x, hi⟩
  have hH (a b : X × I) (x : ↥(W a ⊓ W b)) : H a.1 a.2 b.2 := by
    by_contra h
    have hxD := hOD a.1 a.2 b.2 x.property.1.1
    have hxK : x.val ∈ K a.2 ∩ K b.2 :=
      ⟨subset_closure x.property.1.2, subset_closure x.property.2.2⟩
    change x.val ∈ D a.1 a.2 b.2 at hxD
    dsimp only [D] at hxD
    rw [dite_eq_right h] at hxD
    exact hxD hxK
  have hIn (a b : X × I) (h : H a.1 a.2 b.2) :
      W a ⊓ W b ≤ L a.1 a.2 b.2 h := by
    intro x hx
    have hxD := hOD a.1 a.2 b.2 hx.1.1
    simpa only [D, dite_eq_left h] using hxD
  let primitive (a a' : X × I) : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains A (TopCat.of ↥(W a ⊓ W a'))).X n :=
    if h : H a.1 a.2 a'.2 then
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback A ((Opens.toTopCat X).map (homOfLE (hIn a a' h)))).f n
        (b a.1 a.2 a'.2 h)
    else 0
  refine ⟨⟨W, hWU, hWc, primitive, ?_⟩⟩
  intro a a'
  dsimp only [primitive]
  split_ifs with h
  · have hh := AlgebraicTopology.Cohomology.Singular.LocalPrimitives.cochainMap_primitive
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback A ((Opens.toTopCat X).map (homOfLE (hIn a a' h)))) n _ _
        (hb a.1 a.2 a'.2 h)
    have he : (Opens.toTopCat X).map (homOfLE (hIn a a' h)) ≫
        (Opens.toTopCat X).map (homOfLE (hLU a.1 a.2 a'.2 h)) =
        (Opens.toTopCat X).map (homOfLE (inf_le_inf (hWU a) (hWU a'))) := by
      ext x
      rfl
    rw [← he, AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp]
    exact hh
  · let : IsEmpty ↥(W a ⊓ W a') := ⟨fun x => h (hH a a' x)⟩
    have hz := (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.up ℕ) (n + 1)).map_isZero
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.singularCochains_isZero_of_isEmpty A (TopCat.of ↥(W a ⊓ W a')))
    exact (ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _

end

/-! A genuine singular two-cocycle admits two successive local primitives. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj.RationalCech

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

abbrev singularSectionRestriction (n : ℕ) {U V : Opens X} (h : V ≤ U) :=
  (((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X n).map (homOfLE h).op).hom

theorem singularSectionRestriction_comp (n : ℕ) {U V W : Opens X}
    (hVU : V ≤ U) (hWV : W ≤ V)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)).X n) :
    singularSectionRestriction n hWV (singularSectionRestriction n hVU b) =
      singularSectionRestriction n (hWV.trans hVU) b :=
  Rational.Cech.RationalCech.cechSection_restrict_trans ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X n) hVU hWV b

theorem singularSectionRestriction_d (n : ℕ) {U V : Opens X} (h : V ≤ U)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)).X n) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of V)).d n (n + 1)
        (singularSectionRestriction n h b) =
      singularSectionRestriction (n + 1) h
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)).d n (n + 1) b) :=
  AlgebraicTopology.Cohomology.Singular.LocalPrimitives.cochainMap_primitive (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ)
    ((Opens.toTopCat X).map (homOfLE h))) n _ _ rfl

structure SingularCechDescentData (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2)
    {I : Type} (U : I → Opens X) where
  vertical : Rational.Cech.RationalCech.CechCochain ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 1) U 0
  vertical_d : Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 1 2) 0
    vertical = (Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f 2 c.val
  horizontal : Rational.Cech.RationalCech.CechCochain ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1
  horizontal_d : Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d 0 1) 1
    horizontal = Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 1) U 0 vertical

theorem exists_singularCechDescentData [CompactSpace X] [NormalSpace X]
    [StronglyLocallyContractibleSpace X] (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2) :
    ∃ (I : Type) (U : I → Opens X), (∀ x, ∃ i, x ∈ U i) ∧
      Nonempty (SingularCechDescentData c U) := by
  classical
  let p := PrimitiveCover.singularTwoPrimitiveCover X c
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (p.cover i : Set X)) (fun i => (p.cover i).isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr (p.covers x))
  have hsc : ∀ x, ∃ i : s, x ∈ p.cover i.val := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
    obtain ⟨his, hxi⟩ := Set.mem_iUnion.mp hi
    exact ⟨⟨i, his⟩, hxi⟩
  obtain ⟨r⟩ := nonempty_singularPairPrimitiveRefinement
    (fun i : s => p.cover i.val) 0 (fun i j => p.overlapCocycle i.val j.val) hsc
  let U := r.cover
  let parent : X × s → X := fun a => a.2.val
  have hparent (a : X × s) : U a ≤ p.cover (parent a) := r.subset a
  have hsingle (a : Fin 1 → X × s) : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a ≤ p.cover (parent (a 0)) :=
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0).trans (hparent (a 0))
  have hpair (a : Fin 2 → X × s) : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a ≤ U (a 0) ⊓ U (a 1) :=
    le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)
  let v : Rational.Cech.RationalCech.CechCochain ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 1) U 0 :=
    fun a => singularSectionRestriction 1 (hsingle a) (p.primitive (parent (a 0)))
  let h : Rational.Cech.RationalCech.CechCochain ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1 :=
    fun a => singularSectionRestriction 0 (hpair a) (r.primitive (a 0) (a 1))
  refine ⟨X × s, U, r.covers, ⟨⟨v, ?_, h, ?_⟩⟩⟩
  · funext a
    change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).d 1 2
      (singularSectionRestriction 1 (hsingle a) (p.primitive (parent (a 0)))) = _
    rw [singularSectionRestriction_d, p.differential]
    rw [Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation_apply]
    have he : (Opens.toTopCat X).map (homOfLE (hsingle a)) ≫
        Opens.inclusion' (p.cover (parent (a 0))) =
        (show TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) ⟶ X from
          TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) := by ext x; rfl
    rw [← he, AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp]
    rfl
  · funext a
    change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).d 0 1
      (singularSectionRestriction 0 (hpair a) (r.primitive (a 0) (a 1))) = _
    rw [singularSectionRestriction_d, r.differential]
    change singularSectionRestriction 1 (hpair a)
      (singularSectionRestriction 1 (inf_le_inf (hparent (a 0)) (hparent (a 1)))
        (p.overlapDifference (parent (a 0)) (parent (a 1)))) = _
    rw [singularSectionRestriction_comp, PrimitiveCover.SingularTwoPrimitiveCover.overlapDifference]
    simp only [map_sub]
    change singularSectionRestriction 1 _ (singularSectionRestriction 1 _
        (p.primitive (parent (a 1)))) -
      singularSectionRestriction 1 _ (singularSectionRestriction 1 _
        (p.primitive (parent (a 0)))) = Rational.Cech.RationalCech.cechDelta _ U 0 v a
    rw [Rational.Cech.RationalCech.cechDelta_apply]
    erw [Fin.sum_univ_two, pow_zero, pow_one, one_zsmul, neg_one_zsmul]
    change singularSectionRestriction 1 _ (singularSectionRestriction 1 _ _) -
        singularSectionRestriction 1 _ (singularSectionRestriction 1 _ _) =
      singularSectionRestriction 1 _ (singularSectionRestriction 1 _ _) +
        -(singularSectionRestriction 1 _ (singularSectionRestriction 1 _ _))
    rw [singularSectionRestriction_comp, singularSectionRestriction_comp,
      singularSectionRestriction_comp, singularSectionRestriction_comp, sub_eq_add_neg]
    rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.CechDescent
