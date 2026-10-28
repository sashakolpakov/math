import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.Localization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuativeCenterFields
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.FunctionOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalOrder

/-! # Divisor Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorRestriction

noncomputable section

/-! Rational divisor orders restrict from an integral scheme to the
spectrum of any stalk, with the canonical fraction-field coordinates. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

universe u

variable (X : Scheme.{u}) [IsIntegral X] (x : X)

def fieldMap : X.functionField ⟶ (Spec (X.presheaf.stalk x)).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (X.fromSpecStalk x) (Stalk.Localization.genericPoint_image X x)

instance : IsIso (fieldMap X x) := by
  let := Stalk.Localization.stalkMap_isIso X x (genericPoint (Spec (X.presheaf.stalk x)))
  unfold fieldMap Cycles.Functoriality.FunctionFields.Construction.genericFieldMap
  infer_instance

theorem fieldMap_eq_inverse :
    fieldMap X x = (Affine.FractionField.fieldIso (X.presheaf.stalk x) X.functionField).inv := by
  have hi : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      X.fromSpecStalk x = Normalization.Scheme.genericMap X :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)
  have he := ValuativeCenterFields.liftFieldMap_square (X.presheaf.stalk x) (X.fromSpecStalk x) hi
  exact (Iso.comp_hom_eq_id _).mp he

variable [IsLocallyNoetherian X]

theorem ord_stalk (f : X.functionField) (p : Spec (X.presheaf.stalk x)) :
    (Spec (X.presheaf.stalk x)).ord (fieldMap X x f) p = X.ord f (X.fromSpecStalk x p) := by
  let i := X.fromSpecStalk x
  have hc : coheight (i p) = coheight p := Stalk.Localization.coheight_image X x p
  by_cases hp : coheight p = 1
  · let : Ring.KrullDimLE 1 ((Spec (X.presheaf.stalk x)).presheaf.stalk p) :=
      krullDimLE_of_coheight_le hp.le
    let : Ring.KrullDimLE 1 (X.presheaf.stalk (i p)) :=
      krullDimLE_of_coheight_le (hc.trans hp).le
    let : IsIso (i.stalkMap p) := Stalk.Localization.stalkMap_isIso X x p
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hp,
      Scheme.ord_eq_ordHom_of_coheight_eq_one (hc.trans hp)]
    exact congrArg WithZero.log (OrderQuotientTransport.ordFrac_equiv
      (asIso (i.stalkMap p)).commRingCatIsoToRingEquiv
      (asIso (fieldMap X x)).commRingCatIsoToRingEquiv
      (Divisor.DivisorRestriction.genericFieldMap_stalk i
        (Stalk.Localization.genericPoint_image X x) p) f)
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hp,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hp (hc.symm.trans h))]

theorem order_of_local_element (r : X.presheaf.stalk x) (hr : r ≠ 0)
    (p : Spec (X.presheaf.stalk x)) (hp : p.asIdeal.height = 1) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField r) (X.fromSpecStalk x p) =
      ((Ring.ord (Localization.AtPrime p.asIdeal)
        (algebraMap (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal) r)).toNat : ℤ) := by
  rw [← ord_stalk X x, fieldMap_eq_inverse]
  exact Affine.PrincipalOrder.affine_field_order (X.presheaf.stalk x) X.functionField p hp r hr

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorRestriction
