import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.EtaleRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ResidueDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardComposition

/-! # Etale Support Points -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.EtaleSupportPoints

noncomputable section

/-! Points over the finite etale support open have positive native
residue degree and the exact codimension required by pushforward. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map

theorem residueDegree {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier) (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme W) :
    (Support.Map.supportImageMap f W).residueDegree x = f.left.residueDegree (CycleClass.Geometric.GenericPoint.reducedSupportι W x) := by
  calc
    _ = (Support.Map.supportImageMap f W ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W)).residueDegree x :=
      (Support.Map.residueDegree_post_immersion (Support.Map.supportImageMap f W) (CycleClass.Geometric.GenericPoint.reducedSupportι (ProperCycleLinearity.imageSupport f W)) x).symm
    _ = (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f.left).residueDegree x := by rw [Support.Map.supportImageMap_inclusion]; rfl
    _ = _ := Support.Map.residueDegree_pre_immersion (CycleClass.Geometric.GenericPoint.reducedSupportι W) f.left x

theorem positive {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier) (U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens)
    [Etale (U.ι ≫ Support.Map.supportImageMap f W)] (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme W)
    (hx : Support.Map.supportImageMap f W x ∈ Proper.EtaleRestriction.good (Support.Map.supportImageMap f W) U) :
    0 < f.left.residueDegree (CycleClass.Geometric.GenericPoint.reducedSupportι W x) := by
  let u := Support.Map.supportImageMap f W
  let V := Proper.EtaleRestriction.good u U
  let : IsFinite (u ∣_ V) := Proper.EtaleRestriction.finite u U
  let x' : (u ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  have hp := ResidueDegree.positive (u ∣_ V) x'
  have he : (u ∣_ V).residueDegree x' = u.residueDegree x := by
    rw [← Support.Map.residueDegree_post_immersion (u ∣_ V) V.ι x', morphismRestrict_ι,
      Support.Map.residueDegree_pre_immersion]
    rfl
  rw [he] at hp
  exact (EtaleSupportPoints.residueDegree f W x) ▸ hp

theorem codimension {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (m n k l : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (hd : k + n = l + m) (W : IrreducibleCloseds X.carrier) (U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens)
    [Etale (U.ι ≫ Support.Map.supportImageMap f W)] (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme W)
    (hx : Support.Map.supportImageMap f W x ∈ Proper.EtaleRestriction.good (Support.Map.supportImageMap f W) U)
    (D : Y.DimensionCycleSupport l) (hy : f.left (CycleClass.Geometric.GenericPoint.reducedSupportι W x) = CycleClass.Thom.IntersectionGeometry.supportPoint D.val) :
    X.supportCodimension (irreducibleSetEquivPoints.symm (CycleClass.Geometric.GenericPoint.reducedSupportι W x)) = k := by
  let C := irreducibleSetEquivPoints.symm (CycleClass.Geometric.GenericPoint.reducedSupportι W x)
  have hp : CycleClass.Thom.IntersectionGeometry.supportPoint C = CycleClass.Geometric.GenericPoint.reducedSupportι W x := irreducibleSetEquivPoints.apply_symm_apply _
  have hIm : ProperCycleLinearity.imageSupport f C = D.val := by
    apply irreducibleSetEquivPoints.injective
    exact (irreducibleSetEquivPoints.apply_symm_apply _).trans ((congrArg f.left hp).trans hy)
  have hn : f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint C) ≠ 0 := by
    rw [hp]
    exact Nat.ne_of_gt (positive f W U x hx)
  have he := PushforwardComposition.Grading.support_dimension_eq_of_degree f C hn
  rw [hIm] at he
  have hC := Grading.supportDimension_add_codimension X m C
  have hD := Grading.supportDimension_add_codimension Y n D.val
  rw [D.property] at hD
  change X.supportCodimension C = k
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.EtaleSupportPoints
