import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuativeCenter
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.PointField
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalStalk

/-! # Valuative Center Fields -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuativeCenterFields

noncomputable section

/-! A valuative lift of the actual generic-point map is birational with
the prescribed function-field coordinates. At valuation-ring centers its
native local-ring map is an isomorphism. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuativeCenter

universe u

variable {X : Scheme.{u}} [IsIntegral X]
  (R : Type u) [CommRing R] [IsDomain R]
  [Algebra R X.functionField] [IsFractionRing R X.functionField]
  (i : Spec (.of R) ⟶ X)
  (hi : Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ i = Normalization.Scheme.genericMap X)

theorem liftFieldMap_square :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (ValuativeCenter.lift_genericPoint R i hi) ≫
      (Affine.FractionField.fieldIso R X.functionField).hom = 𝟙 X.functionField := by
  have h := Generic.Fields.genericFieldMap_comp
    (Spec.map (CommRingCat.ofHom (algebraMap R X.functionField))) i
    (Affine.FractionField.genericMap_genericPoint R X.functionField) (ValuativeCenter.lift_genericPoint R i hi)
  have hc := Generic.Fields.genericFieldMap_congr hi
    ((congrArg i (Affine.FractionField.genericMap_genericPoint R X.functionField)).trans
      (ValuativeCenter.lift_genericPoint R i hi)) (Normalization.Scheme.genericMap_apply X _)
  rw [hc, Generic.PointField.genericMap_fieldMap, Affine.FractionField.genericMap_fieldMap] at h
  have he := congrArg (fun t : X.functionField ⟶ (Spec X.functionField).functionField =>
    t ≫ (SpecField.fieldIso X.functionField).inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm

theorem liftFieldMap_isIso : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (ValuativeCenter.lift_genericPoint R i hi)) := by
  let : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (ValuativeCenter.lift_genericPoint R i hi) ≫
      (Affine.FractionField.fieldIso R X.functionField).hom) := by
    rw [liftFieldMap_square R i hi]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (Affine.FractionField.fieldIso R X.functionField).hom

theorem liftFieldMap_apply (g : X.functionField) :
    (Affine.FractionField.fieldIso R X.functionField).hom
      (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (ValuativeCenter.lift_genericPoint R i hi) g) = g :=
  congrArg (fun t : X.functionField ⟶ X.functionField => t g) (liftFieldMap_square R i hi)

include hi in
theorem lift_stalkMap_isIso (r : Spec (.of R)) [ValuationRing (X.presheaf.stalk (i r))] :
    IsIso (i.stalkMap r) := by
  let := liftFieldMap_isIso R i hi
  exact BirationalStalk.stalkMap_isIso_of_valuation i (ValuativeCenter.lift_genericPoint R i hi) r

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuativeCenterFields
