import OAI.AlgebraicGeometry.Divisors.LineBundles.ValuativeCenterPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalValuationOf

/-! # Valuative Center Is -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ValuativeCenterIs.BundleCycles.ValuativeCenterFields

noncomputable section

/-! A valuative lift of the actual generic-point map is birational with
the prescribed function-field coordinates. At valuation-ring centers its
native local-ring map is an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.Divisors.LineBundles.ValuativeCenterPoint.BundleCycles.ValuativeCenter

universe u

variable {X : Scheme.{u}} [IsIntegral X]
  (R : Type u) [CommRing R] [IsDomain R]
  [Algebra R X.functionField] [IsFractionRing R X.functionField]
  (i : Spec (.of R) ⟶ X)
  (hi : Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ i = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X)

theorem liftFieldMap_square :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (ValuativeCenterPoint.BundleCycles.ValuativeCenter.lift_genericPoint R i hi) ≫
      (Affine.FractionField.BundleCycles.AffineFractionField.fieldIso R X.functionField).hom = 𝟙 X.functionField := by
  have h := GenericFieldComposition.BundleCycles.genericFieldMap_comp
    (Spec.map (CommRingCat.ofHom (algebraMap R X.functionField))) i
    (Affine.FractionField.BundleCycles.AffineFractionField.genericMap_genericPoint R X.functionField) (ValuativeCenterPoint.BundleCycles.ValuativeCenter.lift_genericPoint R i hi)
  have hc := GenericFieldComposition.BundleCycles.genericFieldMap_congr hi
    ((congrArg i (Affine.FractionField.BundleCycles.AffineFractionField.genericMap_genericPoint R X.functionField)).trans
      (ValuativeCenterPoint.BundleCycles.ValuativeCenter.lift_genericPoint R i hi)) (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap_apply X _)
  rw [hc, GenericPoint.BundleCycles.GenericPointField.genericMap_fieldMap, Affine.FractionField.BundleCycles.AffineFractionField.genericMap_fieldMap] at h
  have he := congrArg (fun t : X.functionField ⟶ (Spec X.functionField).functionField =>
    t ≫ (SpecFieldOf.BundleCycles.SpecField.fieldIso X.functionField).inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm

theorem liftFieldMap_isIso : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (ValuativeCenterPoint.BundleCycles.ValuativeCenter.lift_genericPoint R i hi)) := by
  let : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (ValuativeCenterPoint.BundleCycles.ValuativeCenter.lift_genericPoint R i hi) ≫
      (Affine.FractionField.BundleCycles.AffineFractionField.fieldIso R X.functionField).hom) := by
    rw [liftFieldMap_square R i hi]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (Affine.FractionField.BundleCycles.AffineFractionField.fieldIso R X.functionField).hom

theorem liftFieldMap_apply (g : X.functionField) :
    (Affine.FractionField.BundleCycles.AffineFractionField.fieldIso R X.functionField).hom
      (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (ValuativeCenterPoint.BundleCycles.ValuativeCenter.lift_genericPoint R i hi) g) = g :=
  congrArg (fun t : X.functionField ⟶ X.functionField => t g) (liftFieldMap_square R i hi)

include hi in
theorem lift_stalkMap_isIso (r : Spec (.of R)) [ValuationRing (X.presheaf.stalk (i r))] :
    IsIso (i.stalkMap r) := by
  let := liftFieldMap_isIso R i hi
  exact BirationalValuationOf.BundleCycles.BirationalValuationStalk.stalkMap_isIso_of_valuation i (ValuativeCenterPoint.BundleCycles.ValuativeCenter.lift_genericPoint R i hi) r

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ValuativeCenterIs.BundleCycles.ValuativeCenterFields
