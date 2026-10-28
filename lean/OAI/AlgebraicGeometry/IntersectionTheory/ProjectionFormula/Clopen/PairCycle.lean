import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Iff
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Pair Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.PairCycle

noncomputable section

/-! Proper meeting and the finite native pair cycle commute with open
and closed restriction, in all codimensions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Cycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (i : V.toOver ⟶ X.toOver)
  [IsOpenImmersion i.left] (m : ℕ)
  [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]

theorem pair_proper_image (p q : ℕ) (A : V.DimensionCycleSupport p) (B : V.DimensionCycleSupport q) :
    Supports.ProperCycle.pairMeetsProperly X p q (Cycle.supportImage i m p A) (Cycle.supportImage i m q B) ↔
      Supports.ProperCycle.pairMeetsProperly V p q A B := by
  constructor
  · intro h D hD
    have hh := h (ProperCycleLinearity.imageSupport i D) (by
      change (ProperCycleLinearity.imageSupport i D : Set X.carrier) ⊆
        (ProperCycleLinearity.imageSupport i A.val : Set X.carrier) ∩ ProperCycleLinearity.imageSupport i B.val
      rw [ProperCycleLinearity.imageSupport_eq_image, ProperCycleLinearity.imageSupport_eq_image, ProperCycleLinearity.imageSupport_eq_image]
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, (hD hx).1, rfl⟩, ⟨x, (hD hx).2, rfl⟩⟩)
    rwa [Cycle.image_codimension i m] at hh
  · intro h D hD
    have hd : (D : Set X.carrier) ⊆ Set.range i.left := by
      intro x hx
      have hxA := (hD hx).1
      change x ∈ (ProperCycleLinearity.imageSupport i A.val : Set X.carrier) at hxA
      rw [ProperCycleLinearity.imageSupport_eq_image] at hxA
      obtain ⟨y, _, rfl⟩ := hxA
      exact Set.mem_range_self y
    let E := Cycle.preimage i D hd
    have he : (E : Set V.carrier) ⊆ (A.val : Set V.carrier) ∩ B.val := by
      intro y hy
      have hyD : i.left y ∈ (D : Set X.carrier) := by
        change y ∈ (Cycle.preimage i D hd : Set V.carrier) at hy
        rwa [Cycle.preimage_coe i D hd] at hy
      have hh := hD hyD
      change i.left y ∈ (ProperCycleLinearity.imageSupport i A.val : Set X.carrier) ∩ ProperCycleLinearity.imageSupport i B.val at hh
      rw [ProperCycleLinearity.imageSupport_eq_image, ProperCycleLinearity.imageSupport_eq_image] at hh
      obtain ⟨a, ha, hay⟩ := hh.1
      obtain ⟨b, hb, hby⟩ := hh.2
      exact ⟨i.left.isOpenEmbedding.injective hay ▸ ha, i.left.isOpenEmbedding.injective hby ▸ hb⟩
    have hh := h E he
    rw [← Cycle.image_codimension i m, Cycle.image_preimage] at hh
    exact hh

theorem pairCycle_restrict_image (p q : ℕ) (A : V.DimensionCycleSupport p) (B : V.DimensionCycleSupport q) :
    CycleMaps.restrict i m (p + q) (Supports.ProperCycle.pairCycle X m p q (Cycle.supportImage i m p A) (Cycle.supportImage i m q B)) =
      Supports.ProperCycle.pairCycle V m p q A B := by
  by_cases h : Supports.ProperCycle.pairMeetsProperly V p q A B
  · ext D
    rw [CycleMaps.restrict_apply, Supports.ProperCycle.pairCycle_apply X m p q _ _ ((pair_proper_image i m p q A B).mpr h),
      Supports.ProperCycle.pairCycle_apply V m p q A B h]
    exact (Iff.multiplicity_image i m A.val B.val D.val).symm
  · have hn := fun hh => h ((pair_proper_image i m p q A B).mp hh)
    rw [Supports.ProperCycle.pairCycle, dite_eq_right hn, map_zero, Supports.ProperCycle.pairCycle, dite_eq_right h]

variable [IsClosedImmersion i.left]

theorem pairCycle_restrict_outside_left (p q : ℕ) (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q)
    (hA : ¬ (A.val : Set X.carrier) ⊆ Set.range i.left) : CycleMaps.restrict i m (p + q) (Supports.ProperCycle.pairCycle X m p q A B) = 0 := by
  by_cases hp : Supports.ProperCycle.pairMeetsProperly X p q A B
  · ext D
    rw [CycleMaps.restrict_apply, Supports.ProperCycle.pairCycle_apply X m p q A B hp, Finsupp.zero_apply, CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity]
    apply dite_eq_right
    intro hx
    exact hA (Cycle.subset_range_of_mem i A.val _ hx.1 ⟨CycleClass.Thom.IntersectionGeometry.supportPoint D.val, (Cycle.image_point i D.val).symm⟩)
  · rw [Supports.ProperCycle.pairCycle, dite_eq_right hp, map_zero]

theorem pairCycle_restrict_outside_right (p q : ℕ) (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q)
    (hB : ¬ (B.val : Set X.carrier) ⊆ Set.range i.left) : CycleMaps.restrict i m (p + q) (Supports.ProperCycle.pairCycle X m p q A B) = 0 := by
  by_cases hp : Supports.ProperCycle.pairMeetsProperly X p q A B
  · ext D
    rw [CycleMaps.restrict_apply, Supports.ProperCycle.pairCycle_apply X m p q A B hp, Finsupp.zero_apply, CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity]
    apply dite_eq_right
    intro hx
    exact hB (Cycle.subset_range_of_mem i B.val _ hx.2 ⟨CycleClass.Thom.IntersectionGeometry.supportPoint D.val, (Cycle.image_point i D.val).symm⟩)
  · rw [Supports.ProperCycle.pairCycle, dite_eq_right hp, map_zero]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.PairCycle
