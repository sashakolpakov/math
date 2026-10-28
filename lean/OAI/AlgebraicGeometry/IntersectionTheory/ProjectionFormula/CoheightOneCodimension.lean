import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveSupports

/-! # Coheight One Codimension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoheightOneCodimension

noncomputable section

/-! Native scheme coheight one agrees with the dimension grading
on every smooth projective presentation. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image

theorem integral (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (W : IrreducibleCloseds X.carrier) (hW : Order.coheight (CycleClass.Thom.IntersectionGeometry.supportPoint W) = 1) :
    X.supportCodimension W = 1 := by
  have hd := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one X.structureMap (CycleClass.Thom.IntersectionGeometry.supportPoint W) hW
  have he : irreducibleSetEquivPoints.symm (CycleClass.Thom.IntersectionGeometry.supportPoint W) = W := irreducibleSetEquivPoints.symm_apply_apply W
  rw [he, Grading.integral_dimension_of_relativeDimension X.structureMap m] at hd
  have hc := Grading.supportDimension_add_codimension X m W
  omega

theorem codimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : IrreducibleCloseds X.carrier) (hW : Order.coheight (CycleClass.Thom.IntersectionGeometry.supportPoint W) = 1) :
    X.supportCodimension W = 1 := by
  let C := X.supportComponent W
  let V := (X.componentVariety C).presentation
  let Z := X.componentSupportPreimage C W (X.support_subset_component W)
  let : SmoothOfRelativeDimension m V.structureMap := Component.Image.component_relativeDimension X m C
  have he : X.componentSupportImage C Z = W := X.componentSupportImage_preimage C W _
  have hp : X.componentInclusion C (CycleClass.Thom.IntersectionGeometry.supportPoint Z) = CycleClass.Thom.IntersectionGeometry.supportPoint W :=
    (X.componentSupportImage_genericPoint C Z).symm.trans (congrArg CycleClass.Thom.IntersectionGeometry.supportPoint he)
  have hz : Order.coheight (CycleClass.Thom.IntersectionGeometry.supportPoint Z) = 1 := by
    rw [← coheight_eq_of_isOpenImmersion (X.componentInclusion C), hp]
    exact hW
  have h := integral V m Z hz
  rw [← Component.Image.image_codimension X C Z, he] at h
  exact h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoheightOneCodimension
