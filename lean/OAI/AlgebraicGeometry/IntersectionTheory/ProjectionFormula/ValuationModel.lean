import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuativeCenterFields
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalLocalSection
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.StalkIso

/-! # Valuation Model -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuationModel

noncomputable section

/-! Birational affine models preserve orders and residue degrees at
valuation-ring centers, without restricting the ambient scheme dimension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuativeCenter OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuativeCenterFields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FractionField

universe u

variable {X : Scheme.{u}} [IsIntegral X]
  (A : Type u) [CommRing A] [IsDomain A] [Algebra A X.functionField] [IsFractionRing A X.functionField]
  (i : Spec (.of A) ⟶ X)
  (hi : Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) ≫ i = Normalization.Scheme.genericMap X)
  (hval : ∀ a : Spec (.of A), ValuationRing (X.presheaf.stalk (i a)))

include hi hval

theorem residueDegree (a : Spec (.of A)) : i.residueDegree a = 1 := by
  let := hval a
  let := ValuativeCenterFields.lift_stalkMap_isIso A i hi a
  exact Stalk.ResidueDegree.residueDegree_of_isIso_stalkMap i a

theorem injective : Function.Injective i := by
  let := ValuativeCenterFields.liftFieldMap_isIso A i hi
  intro a b hab
  let := hval a
  exact BirationalLocalSection.valuationFiber_unique i (ValuativeCenter.lift_genericPoint A i hi)
    (i a) a b rfl hab.symm

theorem ord [IsNoetherianRing A] [IsLocallyNoetherian X]
    (g : X.functionField) (a : Spec (.of A)) :
    (Spec (.of A)).ord ((Affine.FractionField.fieldIso A X.functionField).inv g) a = X.ord g (i a) := by
  let := hval a
  let := ValuativeCenterFields.liftFieldMap_isIso A i hi
  let := ValuativeCenterFields.lift_stalkMap_isIso A i hi a
  have he : (Affine.FractionField.fieldIso A X.functionField).inv g =
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (ValuativeCenter.lift_genericPoint A i hi) g := by
    apply (Affine.FractionField.fieldIso A X.functionField).commRingCatIsoToRingEquiv.injective
    exact ((Affine.FractionField.fieldIso A X.functionField).commRingCatIsoToRingEquiv.apply_symm_apply g).trans
      (ValuativeCenterFields.liftFieldMap_apply A i hi g).symm
  rw [he]
  exact Divisor.StalkIso.ord_eq_of_stalkMap_isIso i (ValuativeCenter.lift_genericPoint A i hi) a
    (BirationalStalk.coheight_of_valuation i (ValuativeCenter.lift_genericPoint A i hi) a) g

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuationModel
