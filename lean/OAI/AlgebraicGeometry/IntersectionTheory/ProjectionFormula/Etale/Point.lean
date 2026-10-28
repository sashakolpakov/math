import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.SupportEtaleOpen
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProperMoving

/-! # Point -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.Point

noncomputable section

/-! Proper position against the exceptional supports puts every
expected intersection point in the finite etale target open. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map

theorem mem_good {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier) (U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens)
    (F : Finset (IrreducibleCloseds Y.carrier))
    (hcod : ∀ D ∈ F, Y.supportCodimension (ProperCycleLinearity.imageSupport f W) < Y.supportCodimension D)
    (hcover : ∀ x : CycleClass.Geometric.GenericPoint.reducedSupportScheme W, x ∉ U →
      ∃ D ∈ F, f.left (CycleClass.Geometric.GenericPoint.reducedSupportι W x) ∈ (D : Set Y.carrier))
    (p : ℕ) (A : Y.DimensionCycleSupport p) (hA : Relative.ProperMoving.ProperAgainst Y p A F)
    (C : Y.DimensionCycleSupport (p + Y.supportCodimension (ProperCycleLinearity.imageSupport f W)))
    (hcA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set Y.carrier))
    (hcW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (ProperCycleLinearity.imageSupport f W : Set Y.carrier)) :
    CycleClass.Thom.IntersectionGeometry.supportPreimage (ProperCycleLinearity.imageSupport f W) (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hcW ∈
      Proper.EtaleRestriction.good (Support.Map.supportImageMap f W) U := by
  rintro ⟨x, hx, he⟩
  obtain ⟨D, hD, hxD⟩ := hcover x hx
  have hpoint : f.left (CycleClass.Geometric.GenericPoint.reducedSupportι W x) = CycleClass.Thom.IntersectionGeometry.supportPoint C.val := by
    have h := congrArg (fun g : CycleClass.Geometric.GenericPoint.reducedSupportScheme W ⟶ Y.carrier => g x)
      (Support.Map.supportImageMap_inclusion f W)
    change CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W) (Support.Map.supportImageMap f W x) = f.left (CycleClass.Geometric.GenericPoint.reducedSupportι W x) at h
    exact h.symm.trans ((congrArg (CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W)) he).trans
      (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec (ProperCycleLinearity.imageSupport f W) _ hcW))
  rw [hpoint] at hxD
  have hC : (C.val : Set Y.carrier) ⊆ (A.val : Set Y.carrier) ∩ D :=
    (Supports.supportPoint_mem_iff_subset
      (⟨(A.val : Set Y.carrier) ∩ D, A.val.isClosed.inter D.isClosed⟩ : Closeds Y.carrier) C.val).mp ⟨hcA, hxD⟩
  have hp := hA D hD C.val hC
  have hh := hcod D hD
  rw [C.property] at hp
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.Point
