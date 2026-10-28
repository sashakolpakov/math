import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FractionField
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.DivisorRestriction

/-! # Function Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.FunctionOrder

noncomputable section

/-! Regular functions have nonnegative order. The affine formulation
uses a specified fraction field and the native function-field isomorphism. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

theorem stalk_nonneg {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (a : X.presheaf.stalk x) :
    0 ≤ X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hx : coheight x = 1
  · let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
    change 0 ≤ WithZero.log (Ring.ordFrac (X.presheaf.stalk x)
      (algebraMap (X.presheaf.stalk x) X.functionField a))
    have h := Ring.ordFrac_ge_one_of_ne_zero (K := X.functionField) ha
    exact (WithZero.le_log_iff_exp_le (ne_zero_of_lt (zero_lt_one.trans_le h))).mpr h
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx]

theorem affine_nonneg (A L : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Field L] [Algebra A L] [IsFractionRing A L] (a : A) (x : Spec (.of A)) :
    0 ≤ (Spec (.of A)).ord ((Affine.FractionField.fieldIso A L).inv (algebraMap A L a)) x := by
  have he : (Affine.FractionField.fieldIso A L).inv (algebraMap A L a) =
      StructureSheaf.toStalk A (genericPoint (Spec (.of A))) a := by
    apply (Affine.FractionField.fieldIso A L).commRingCatIsoToRingEquiv.injective
    exact ((Affine.FractionField.fieldIso A L).commRingCatIsoToRingEquiv.apply_symm_apply _).trans
      (congrArg (fun t : CommRingCat.of A ⟶ CommRingCat.of L => t a)
        (Affine.FractionField.toStalk_fieldIso A L)).symm
  have hs : StructureSheaf.toStalk A (genericPoint (Spec (.of A))) a =
      algebraMap ((Spec (.of A)).presheaf.stalk x) (Spec (.of A)).functionField
        (StructureSheaf.toStalk A x a) := by
    exact (congrArg (fun t : CommRingCat.of A ⟶ (Spec (.of A)).functionField => t a)
      (StructureSheaf.toStalk_stalkSpecializes
        ((genericPoint_spec (Spec (.of A))).specializes trivial))).symm
  rw [he, hs]
  exact stalk_nonneg x (StructureSheaf.toStalk A x a)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.FunctionOrder
