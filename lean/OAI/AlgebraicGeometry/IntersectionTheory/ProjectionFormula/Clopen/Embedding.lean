import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Bilinear
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.Component
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DivisorComponents

/-! # Embedding -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Embedding

noncomputable section

/-! Intersections supported in an open and closed subpresentation can
be computed there and embedded by the native proper pushforward. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Cycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle
  CycleSupport

variable {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left]
  (m : ℕ) [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]

theorem meetProperly_restrict (p q : ℕ) (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b) : CycleClass.Thom.IntersectionGeometry.MeetProperly V p q (CycleMaps.restrict i m p a) (CycleMaps.restrict i m q b) := by
  intro A hA B hB
  have ha : Cycle.supportImage i m p A ∈ a.support := by
    simpa only [Finsupp.mem_support_iff, CycleMaps.restrict_apply] using hA
  have hb : Cycle.supportImage i m q B ∈ b.support := by
    simpa only [Finsupp.mem_support_iff, CycleMaps.restrict_apply] using hB
  exact (PairCycle.pair_proper_image i m p q A B).mp (hp _ ha _ hb)

theorem restrict_preserves_divisor_relations :
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1 ≤ (CycleClass.Thom.IntersectionGeometry.rationalEquivalences V 1).comap (CycleMaps.restrict i m 1) := by
  intro a ha
  change CycleMaps.restrict i m 1 a ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences V 1
  rw [← CycleMaps.flatMap_eq_restrict]
  exact Smooth.DivisorComponents.flatMap_preserves_relations i m m ha

variable [IsClosedImmersion i.left]

theorem supported_embed (q : ℕ) (b : V.RationalDimensionCycle q) :
    CycleSupport.SupportedOn X q (CycleMaps.embed i m q b) ⟨Set.range i.left, i.left.isClosedEmbedding.isClosed_range⟩ := by
  rw [CycleMaps.embed_eq_pushforward]
  apply CycleSupport.pushforward V X i q q b ⟨Set.univ, isClosed_univ⟩
    ⟨Set.range i.left, i.left.isClosedEmbedding.isClosed_range⟩
  · intro A _
    exact Set.subset_univ _
  · rintro _ ⟨x, _, rfl⟩
    exact Set.mem_range_self x

theorem intersection_embed (p q : ℕ) (a : X.RationalDimensionCycle p) (b : V.RationalDimensionCycle q)
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a (CycleMaps.embed i m q b)) :
    Supports.ProperCycle.intersectionBilinear X m p q a (CycleMaps.embed i m q b) =
      CycleMaps.embed i m (p + q) (Supports.ProperCycle.intersectionBilinear V m p q (CycleMaps.restrict i m p a) b) := by
  have he := Bilinear.restrict_bilinear i m p q a (CycleMaps.embed i m q b)
  rw [CycleMaps.restrict_embed] at he
  rw [← he]
  symm
  apply CycleMaps.embed_restrict
  exact General.Component.supported_right X p q _ _ _
    (Supports.ProperCycle.intersectionBilinear_isProper X m p q _ _ hp) _ (supported_embed i m q b)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Embedding
