import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.SupportRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFamilyFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.CycleTransport

/-! # Horizontal Fiber Closed Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFiberClosedRestriction

noncomputable section

/-! A horizontal fiber cycle computed in a closed ambient embedding
is the pushforward of the same native cycle on the contained support. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {Y Z : Scheme} [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.IsNoetherian Z]
  (j : Y ⟶ Z) [IsClosedImmersion j] (C : IrreducibleCloseds Z)
  (hC : (C : Set Z) ⊆ Set.range j) (t : Z ⟶ Spec (.of ℂ[X]))

abbrev support := Closed.SupportRestriction.support j C hC

omit [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.IsNoetherian Z] in
theorem parameter : (Closed.SupportRestriction.iso j C hC).hom ≫
    ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine) =
    ((CycleClass.Geometric.GenericPoint.reducedSupportι (support j C hC) ≫ (j ≫ t)) ≫ Projective.FamilyIs.MatrixParameterOpen.affine) := by
  rw [← Category.assoc, ← Category.assoc, Closed.SupportRestriction.iso_fac]
  simp only [Category.assoc]

variable (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
  (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

omit [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.IsNoetherian Z] in
include hη in
theorem horizontal : ((CycleClass.Geometric.GenericPoint.reducedSupportι (support j C hC) ≫ (j ≫ t)) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
    (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (support j C hC))) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) := by
  exact Parameter.CycleTransport.horizontal (Closed.SupportRestriction.iso j C hC).hom
    _ _ (parameter j C hC t).symm hη

theorem cycle (a : ℂ) :
    CyclePushforward.pointPushforward j (HorizontalFamilyFiber.Family.cycle Y (support j C hC) (j ≫ t)
      (horizontal j C hC t hη) a) = HorizontalFamilyFiber.Family.cycle Z C t hη a := by
  rw [Parameter.CycleTransport.family_formula]
  exact Parameter.CycleTransport.compose_congr (Closed.SupportRestriction.iso j C hC).hom
    _ _ (horizontal j C hC t hη) hη (CycleClass.Geometric.GenericPoint.reducedSupportι C)
    (CycleClass.Geometric.GenericPoint.reducedSupportι (support j C hC) ≫ j) (Closed.SupportRestriction.iso_fac j C hC)
    (parameter j C hC t).symm a (fun z _ => (Closed.SupportRestriction.iso j C hC).hom.surjective z)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFiberClosedRestriction
