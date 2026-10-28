import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.PointCongruence

/-! # Projected Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProjectedSupport

noncomputable section

/-! The proper image of the native incidence locus is exactly the
closed set where the two finite support projections have a common value. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.PointCongruence.SupportData

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
  (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
  (W Z : IrreducibleCloseds X.carrier) (hW : Projection.PointCongruence.SupportData.NoBase X k L W) (hZ : Projection.PointCongruence.SupportData.NoBase X k L Z)

def fiber : Closeds (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) :=
  ⟨Projection.PointCongruence.SupportData.projection X k L Z hZ ⁻¹' Set.range (Projection.PointCongruence.SupportData.projection X k L W hW),
    (by
      have hc : IsClosed (Set.range (Projection.PointCongruence.SupportData.projection X k L W hW)) := by
        simpa only [Set.image_univ] using (Projection.PointCongruence.SupportData.projection X k L W hW).isClosedMap Set.univ isClosed_univ
      exact hc.preimage (Projection.PointCongruence.SupportData.projection X k L Z hZ).continuous)⟩

def intersection : Closeds X.carrier := Proper.ImageBounds.image X (CycleClass.Geometric.GenericPoint.reducedSupportι Z) (fiber X k L W Z hW hZ)

theorem incidence_subset : DisjointIncidenceImage.image X W Z k L ≤ intersection X k L W Z hW hZ := by
  rintro y ⟨a, ha, rfl⟩
  have heq := DefinedPair.Projection.locus_eq X k L (Support.Pair.first X W Z) (Support.Pair.second X W Z)
    (Projection.PointCongruence.SupportData.first_domain X k L W Z hW) (Projection.PointCongruence.SupportData.second_domain X k L W Z hZ)
  have ha' := Eq.mp (congrArg (fun S : Closeds (Support.Pair.space X W Z) => a ∈ S) heq) ha
  have he := Closed.Equalizer.eq_of_mem
    (DefinedPair.Projection.projection X k L (Support.Pair.first X W Z) (Projection.PointCongruence.SupportData.first_domain X k L W Z hW))
    (DefinedPair.Projection.projection X k L (Support.Pair.second X W Z) (Projection.PointCongruence.SupportData.second_domain X k L W Z hZ)) a ha'
  rw [Projection.PointCongruence.SupportData.first_point X k L W Z hW, Projection.PointCongruence.SupportData.second_point X k L W Z hZ] at he
  refine ⟨pullback.snd (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) a, ?_, rfl⟩
  exact ⟨pullback.fst (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) a, he⟩

theorem subset_incidence : intersection X k L W Z hW hZ ≤ DisjointIncidenceImage.image X W Z k L := by
  apply Projection.ProjectionCoincidence.closed_subset X.structureMap
  rintro y ⟨z, ⟨w, hw⟩, hzy⟩ hy
  have hzc : IsClosed ({z} : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)) :=
    Closed.FiberPoints.closed (CycleClass.Geometric.GenericPoint.reducedSupportι Z) z (hzy.symm ▸ hy)
  have hpzc : IsClosed ({Projection.PointCongruence.SupportData.projection X k L Z hZ z} : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace k)) := by
    simpa only [Set.image_singleton] using (Projection.PointCongruence.SupportData.projection X k L Z hZ).isClosedMap _ hzc
  have hwc : IsClosed ({w} : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) :=
    Closed.FiberPoints.closed (Projection.PointCongruence.SupportData.projection X k L W hW) w (hw.symm ▸ hpzc)
  have hwx : IsClosed ({CycleClass.Geometric.GenericPoint.reducedSupportι W w} : Set X.carrier) := by
    simpa only [Set.image_singleton] using (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.isClosedMap _ hwc
  have hzX : IsClosed ({CycleClass.Geometric.GenericPoint.reducedSupportι Z z} : Set X.carrier) := hzy.symm ▸ hy
  have hwW : CycleClass.Geometric.GenericPoint.reducedSupportι W w ∈ (W : Set X.carrier) := by rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι]; exact Set.mem_range_self w
  have hzZ : CycleClass.Geometric.GenericPoint.reducedSupportι Z z ∈ (Z : Set X.carrier) := by rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι]; exact Set.mem_range_self z
  obtain ⟨a, ha, haw, haz⟩ := Support.PairClosedPoints.exists_pair X W Z
    (CycleClass.Geometric.GenericPoint.reducedSupportι W w) (CycleClass.Geometric.GenericPoint.reducedSupportι Z z) hwx hzX hwW hzZ
  have hfst : pullback.fst (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) a = w :=
    (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective haw
  have hsnd : pullback.snd (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap) (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) a = z :=
    (CycleClass.Geometric.GenericPoint.reducedSupportι Z).isClosedEmbedding.injective haz
  have haI : a ∈ Support.PairIncidenceStep.incidence X W Z k L := by
    apply (Projection.PointCongruence.SupportData.mem_incidence X k L W Z hW hZ a ha).mpr
    rw [hfst, hsnd]
    exact hw
  exact ⟨a, haI, haz.trans hzy⟩

theorem image_eq : DisjointIncidenceImage.image X W Z k L = intersection X k L W Z hW hZ :=
  le_antisymm (incidence_subset X k L W Z hW hZ) (subset_incidence X k L W Z hW hZ)

theorem dimension_bound (hd : Disjoint (W : Set X.carrier) (Z : Set X.carrier))
    (hI : Projection.Generic.InductionBounds.incidence X W Z L)
    (C : IrreducibleCloseds X.carrier) (hC : (C : Set X.carrier) ⊆ intersection X k L W Z hW hZ) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension C X.structureMap + k ≤
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.structureMap := by
  apply DisjointIncidenceImage.bound X W Z hd k L hI C
  rw [image_eq X k L W Z hW hZ]
  exact hC

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProjectedSupport
