import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.Point
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.CycleSupport

/-! # Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Moving

noncomputable section

/-! Move a target cycle so that its actual inverse image meets a
fixed support properly and every expected image intersection is in
the finite etale region of the support map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProperMoving

theorem representatives {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m n p q : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (a : Y.RationalDimensionCycle p) (W : X.DimensionCycleSupport q)
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W.val) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W.val X.structureMap) :
    ∃ a' : Y.RationalDimensionCycle p, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent Y p a a' ∧
      CycleClass.Thom.IntersectionGeometry.MeetProperly X p q (ProjectionFormula.Smooth.Cycle.flatMap f p a') (Finsupp.single W 1) ∧
      (∀ A ∈ a'.support, ∀ C : IrreducibleCloseds Y.carrier,
        (C : Set Y.carrier) ⊆ (A.val : Set Y.carrier) ∩ ProperCycleLinearity.imageSupport f W.val →
          p + Y.supportCodimension (ProperCycleLinearity.imageSupport f W.val) ≤ Y.supportCodimension C) ∧
      ∃ U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).Opens,
        genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val) ∈ U ∧ Etale (U.ι ≫ Support.Map.supportImageMap f W.val) ∧
        ∀ A ∈ a'.support, ∀ C : Y.DimensionCycleSupport (p + Y.supportCodimension (ProperCycleLinearity.imageSupport f W.val)),
          ∀ (_hcA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set Y.carrier))
            (hcW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (ProperCycleLinearity.imageSupport f W.val : Set Y.carrier)),
          CycleClass.Thom.IntersectionGeometry.supportPreimage (ProperCycleLinearity.imageSupport f W.val) (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hcW ∈
            Proper.EtaleRestriction.good (Support.Map.supportImageMap f W.val) U := by
  obtain ⟨U, hη, hU, F, hcod, hcover⟩ := SupportEtaleOpen.exists_data f n W.val hd
  obtain ⟨G, hWG, hG⟩ := Relative.ProperMoving.family f m n W.val
  let T := F ∪ G
  obtain ⟨a', ha, hT⟩ := General.ChowMoving.cycle Y n (fun D : T => D.val) p a
  have hf (A : Y.DimensionCycleSupport p) (hA : A ∈ a'.support) : Relative.ProperMoving.ProperAgainst Y p A F := by
    intro D hD C hC
    exact hT ⟨D, Finset.mem_union_left _ hD⟩ A hA C hC
  have hg (A : Y.DimensionCycleSupport p) (hA : A ∈ a'.support) : Relative.ProperMoving.ProperAgainst Y p A G := by
    intro D hD C hC
    exact hT ⟨D, Finset.mem_union_right _ hD⟩ A hA C hC
  refine ⟨a', ha, ?_, ?_, U, hη, hU, ?_⟩
  · intro L hL D hD C hC
    have hDW : D = W := by simpa using hD
    subst D
    obtain ⟨A, hA, _, hLA⟩ := ProjectionFormula.Smooth.CycleSupport.origin f m n p a' L hL
    have he := hG p A (hg A hA) C (fun x hx => ⟨(hC hx).2, hLA (hC hx).1⟩)
    rw [W.property] at he
    omega
  · intro A hA C hC
    exact hg A hA (ProperCycleLinearity.imageSupport f W.val) hWG C hC
  · intro A hA C hcA hcW
    exact ProjectionFormula.Etale.Point.mem_good f W.val U F hcod hcover p A (hf A hA) C hcA hcW

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Moving
