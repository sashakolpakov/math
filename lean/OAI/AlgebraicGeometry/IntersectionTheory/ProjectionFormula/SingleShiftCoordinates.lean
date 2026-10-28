import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.TensorSingle

/-! # Single Shift Coordinates -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SingleShiftCoordinates

noncomputable section

/-! Coordinates of the canonical shift isomorphism for single complexes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory

variable (R : Type) [CommRing R] (M : ModuleCat.{0} R)

theorem shiftIso_term (n d d' : ℤ) (h : n + d = d') :
    (((CochainComplex.singleFunctor (ModuleCat.{0} R) d').obj M).shiftFunctorObjXIso n d d' (by omega)).inv ≫
      (((CochainComplex.singleFunctors (ModuleCat.{0} R)).shiftIso n d d' h).hom.app M).f d ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) d M).hom =
    (HomologicalComplex.singleObjXSelf (.up ℤ) d' M).hom := by
  subst d'
  simp [CochainComplex.singleFunctors, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.single, add_comm]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SingleShiftCoordinates
