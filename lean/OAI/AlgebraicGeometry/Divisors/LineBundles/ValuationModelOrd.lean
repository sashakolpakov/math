import OAI.AlgebraicGeometry.Divisors.LineBundles.ValuativeCenterIs
import OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalValuationComp
import OAI.AlgebraicGeometry.Divisors.LineBundles.MorphismOrderStalk

/-! # Valuation Model Ord -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ValuationModelOrd.BundleCycles.ValuationModel

noncomputable section

/-! Birational affine models preserve orders and residue degrees at
valuation-ring centers, without restricting the ambient scheme dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Divisors.LineBundles.ValuativeCenterPoint.BundleCycles.ValuativeCenter OAI.AlgebraicGeometry.Divisors.LineBundles.ValuativeCenterIs.BundleCycles.ValuativeCenterFields OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.FractionField.BundleCycles.AffineFractionField

universe u

variable {X : Scheme.{u}} [IsIntegral X]
  (A : Type u) [CommRing A] [IsDomain A] [Algebra A X.functionField] [IsFractionRing A X.functionField]
  (i : Spec (.of A) ⟶ X)
  (hi : Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) ≫ i = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X)
  (hval : ∀ a : Spec (.of A), ValuationRing (X.presheaf.stalk (i a)))

include hi hval

theorem residueDegree (a : Spec (.of A)) : i.residueDegree a = 1 := by
  let := hval a
  let := ValuativeCenterIs.BundleCycles.ValuativeCenterFields.lift_stalkMap_isIso A i hi a
  exact BirationalStalk.BundleCycles.BirationalStalkResidueDegree.residueDegree_of_isIso_stalkMap i a

theorem injective : Function.Injective i := by
  let := ValuativeCenterIs.BundleCycles.ValuativeCenterFields.liftFieldMap_isIso A i hi
  intro a b hab
  let := hval a
  exact BirationalValuationComp.BundleCycles.BirationalValuationSection.valuationFiber_unique i (ValuativeCenterPoint.BundleCycles.ValuativeCenter.lift_genericPoint A i hi)
    (i a) a b rfl hab.symm

theorem ord [IsNoetherianRing A] [IsLocallyNoetherian X]
    (g : X.functionField) (a : Spec (.of A)) :
    (Spec (.of A)).ord ((Affine.FractionField.BundleCycles.AffineFractionField.fieldIso A X.functionField).inv g) a = X.ord g (i a) := by
  let := hval a
  let := ValuativeCenterIs.BundleCycles.ValuativeCenterFields.liftFieldMap_isIso A i hi
  let := ValuativeCenterIs.BundleCycles.ValuativeCenterFields.lift_stalkMap_isIso A i hi a
  have he : (Affine.FractionField.BundleCycles.AffineFractionField.fieldIso A X.functionField).inv g =
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (ValuativeCenterPoint.BundleCycles.ValuativeCenter.lift_genericPoint A i hi) g := by
    apply (Affine.FractionField.BundleCycles.AffineFractionField.fieldIso A X.functionField).commRingCatIsoToRingEquiv.injective
    exact ((Affine.FractionField.BundleCycles.AffineFractionField.fieldIso A X.functionField).commRingCatIsoToRingEquiv.apply_symm_apply g).trans
      (ValuativeCenterIs.BundleCycles.ValuativeCenterFields.liftFieldMap_apply A i hi g).symm
  rw [he]
  exact MorphismOrderStalk.BundleCycles.ord_of_stalkMap_isIso i (ValuativeCenterPoint.BundleCycles.ValuativeCenter.lift_genericPoint A i hi) a
    (BirationalValuationOf.BundleCycles.BirationalValuationStalk.coheight_of_valuation i (ValuativeCenterPoint.BundleCycles.ValuativeCenter.lift_genericPoint A i hi) a) g

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ValuationModelOrd.BundleCycles.ValuationModel
