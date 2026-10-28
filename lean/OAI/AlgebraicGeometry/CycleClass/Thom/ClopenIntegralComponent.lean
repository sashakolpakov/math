import OAI.AlgebraicGeometry.CycleClass.Geometric.ProjectiveComponentDimension
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Clopen Integral Component -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ClopenIntegralComponent.Constructions

noncomputable section

/-! A genuine integral open-and-closed subscheme of a smooth projective
presentation is precisely one of its actual integral components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {T : Scheme} [IsIntegral T]
  (i : T ⟶ Z.carrier) [IsOpenImmersion i] [IsClosedImmersion i]

def clopenImageComponent : irreducibleComponents Z.carrier :=
  Z.supportComponent (Geometric.StratumClosure.integralImageClosure i)

theorem clopenImageComponent_range : Set.range i = (clopenImageComponent Z i).val := by
  have hw : (Geometric.StratumClosure.integralImageClosure i : Set Z.carrier) = Set.range i := i.isClosedEmbedding.isClosed_range.closure_eq
  have hs : Set.range i ⊆ (clopenImageComponent Z i).val := by
    rw [← hw]
    exact Z.support_subset_component (Geometric.StratumClosure.integralImageClosure i)
  have hd := subset_closure_inter_of_isPreirreducible_of_isOpen
    (clopenImageComponent Z i).property.1.2 i.isOpenEmbedding.isOpen_range
    (by
      obtain ⟨t⟩ := (inferInstance : Nonempty T)
      exact ⟨i t, hs (Set.mem_range_self t), Set.mem_range_self t⟩)
  rw [Set.inter_eq_right.mpr hs, i.isClosedEmbedding.isClosed_range.closure_eq] at hd
  exact Set.Subset.antisymm hs hd

theorem clopenImageComponent_factor_range : Set.range i ⊆
    Set.range (Z.componentInclusion (clopenImageComponent Z i)) := by
  rw [Z.componentInclusion_range, clopenImageComponent_range]

def clopenComponentMap : T ⟶ (Z.componentVariety (clopenImageComponent Z i)).carrier :=
  IsOpenImmersion.lift (Z.componentInclusion (clopenImageComponent Z i)) i
    (clopenImageComponent_factor_range Z i)

instance clopenComponentMap_open : IsOpenImmersion (clopenComponentMap Z i) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift
    (Z.componentInclusion (clopenImageComponent Z i)) i (clopenImageComponent_factor_range Z i)))

@[reassoc]
theorem clopenComponentMap_inclusion :
    clopenComponentMap Z i ≫ Z.componentInclusion (clopenImageComponent Z i) = i :=
  IsOpenImmersion.lift_fac _ _ _

instance clopenComponentMap_isIso : IsIso (clopenComponentMap Z i) := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, (surjective_iff _).mpr ?_⟩
  intro y
  have hy : Z.componentInclusion (clopenImageComponent Z i) y ∈ Set.range i := by
    rw [clopenImageComponent_range, ← Z.componentInclusion_range]
    exact Set.mem_range_self y
  obtain ⟨t, ht⟩ := hy
  refine ⟨t, (Z.componentInclusion (clopenImageComponent Z i)).isOpenEmbedding.injective ?_⟩
  change (clopenComponentMap Z i ≫ Z.componentInclusion (clopenImageComponent Z i)) t = _
  rw [clopenComponentMap_inclusion]
  exact ht

def clopenComponentIso : T ≅ (Z.componentVariety (clopenImageComponent Z i)).carrier :=
  asIso (clopenComponentMap Z i)

@[reassoc]
theorem clopenComponentMap_base :
    clopenComponentMap Z i ≫ (Z.componentVariety (clopenImageComponent Z i)).structureMap =
      i ≫ Z.structureMap := by
  rw [← Z.componentInclusion_over, clopenComponentMap_inclusion_assoc]

theorem clopenImageComponent_eq_supportComponent (S : IrreducibleCloseds Z.carrier)
    (hS : (S : Set Z.carrier) ⊆ Set.range i) : clopenImageComponent Z i = Z.supportComponent S :=
  (Z.supportComponent_eq_of_subset S (clopenImageComponent Z i)
    (by rwa [← clopenImageComponent_range])).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ClopenIntegralComponent.Constructions
