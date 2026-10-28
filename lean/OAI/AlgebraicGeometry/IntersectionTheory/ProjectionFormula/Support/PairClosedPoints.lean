import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.FiberPoints

/-! # Pair Closed Points -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.PairClosedPoints

noncomputable section

/-! Closed points of two supports determine a closed point of their
actual scheme product over the complex base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair

theorem exists_pair (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W Z : IrreducibleCloseds X.carrier)
    (x y : X.carrier) (hx : IsClosed {x}) (hy : IsClosed {y}) (hxW : x ∈ W) (hyZ : y ∈ Z) :
    ∃ a : Pair.space X W Z, IsClosed {a} ∧ (Pair.first X W Z).left a = x ∧ (Pair.second X W Z).left a = y := by
  have hxW' : x ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W) := by rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]; exact hxW
  have hyZ' : y ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι Z) := by rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]; exact hyZ
  obtain ⟨w, hw⟩ := hxW'
  obtain ⟨z, hz⟩ := hyZ'
  have hwc : IsClosed ({w} : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) :=
    Closed.FiberPoints.closed (CycleClass.Geometric.GenericPoint.reducedSupportι W) w (hw.symm ▸ hx)
  have hzc : IsClosed ({z} : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)) :=
    Closed.FiberPoints.closed (CycleClass.Geometric.GenericPoint.reducedSupportι Z) z (hz.symm ▸ hy)
  let f := CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap
  let g := CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap
  let p := pointOfClosedPoint f w hwc
  let q := pointOfClosedPoint g z hzc
  have hp : p ≫ f = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have hq : q ≫ g = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  let r := pullback.lift p q (hp.trans hq.symm)
  have hr : r ≫ Pair.base X W Z = 𝟙 _ := by
    change (pullback.lift p q _) ≫ pullback.fst f g ≫ f = _
    rw [pullback.lift_fst_assoc]
    exact hp
  refine ⟨r (IsLocalRing.closedPoint ℂ),
    ((pointEquivClosedPoint (Pair.base X W Z)) ⟨r, hr⟩).property, ?_, ?_⟩
  · have he := congrArg (fun a : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme W => a (IsLocalRing.closedPoint ℂ))
      (pullback.lift_fst p q (hp.trans hq.symm))
    change CycleClass.Geometric.GenericPoint.reducedSupportι W (pullback.fst f g (r (IsLocalRing.closedPoint ℂ))) = x
    exact (congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι W) (he.trans (pointOfClosedPoint_apply f w hwc _))).trans hw
  · have he := congrArg (fun a : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme Z => a (IsLocalRing.closedPoint ℂ))
      (pullback.lift_snd p q (hp.trans hq.symm))
    change CycleClass.Geometric.GenericPoint.reducedSupportι Z (pullback.snd f g (r (IsLocalRing.closedPoint ℂ))) = y
    exact (congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι Z) (he.trans (pointOfClosedPoint_apply g z hzc _))).trans hz

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.PairClosedPoints
