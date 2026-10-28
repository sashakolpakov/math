import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.FunctionOrder

/-! # Principal Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalOrder

noncomputable section

/-! The native order of a regular rational function is the length of
its principal quotient, on scheme stalks and on affine localizations. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

universe u

theorem stalk_order (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (hx : coheight x = 1) (a : X.presheaf.stalk x) (ha : a ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x =
      ((Ring.ord (X.presheaf.stalk x) a).toNat : ℤ) := by
  let R := X.presheaf.stalk x
  let : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hx.le
  have hfin : Ring.ord R a = ((Ring.ord R a).toNat : ℕ∞) :=
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))).symm
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
  change WithZero.log (Ring.ordFrac R (algebraMap R X.functionField a)) = _
  rw [Ring.ordFrac_eq_ord R ha,
    Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero ha) hfin]
  rfl

theorem affine_order (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (p : Spec (.of R)) (hp : p.asIdeal.height = 1) (a : R) (ha : a ≠ 0) :
    (Spec (.of R)).ord (StructureSheaf.toStalk R (genericPoint (Spec (.of R))) a) p =
      ((Ring.ord (Localization.AtPrime p.asIdeal)
        (algebraMap R (Localization.AtPrime p.asIdeal) a)).toNat : ℤ) := by
  have hs : StructureSheaf.toStalk R (genericPoint (Spec (.of R))) a =
      algebraMap ((Spec (.of R)).presheaf.stalk p) (Spec (.of R)).functionField
        (StructureSheaf.toStalk R p a) :=
    (congrArg (fun t : CommRingCat.of R ⟶ (Spec (.of R)).functionField => t a)
      (StructureSheaf.toStalk_stalkSpecializes
        ((genericPoint_spec (Spec (.of R))).specializes trivial))).symm
  have helem : (StructureSheaf.stalkIso R p) (algebraMap R (Localization.AtPrime p.asIdeal) a) =
      StructureSheaf.toStalk R p a := (StructureSheaf.stalkIso R p).commutes a
  have hi : Function.Injective (algebraMap R (Localization.AtPrime p.asIdeal)) :=
    IsLocalization.injective _ p.asIdeal.primeCompl_le_nonZeroDivisors
  have hpa : StructureSheaf.toStalk R p a ≠ 0 := by
    rw [← helem]
    exact (map_ne_zero_iff _ (StructureSheaf.stalkIso R p).injective).mpr
      ((map_ne_zero_iff _ hi).mpr ha)
  rw [hs, stalk_order (Spec (.of R)) p ((idealHeight_eq_coheight (.of R) p).symm.trans hp) _ hpa]
  have he := OrderQuotientTransport.ord_equiv (StructureSheaf.stalkIso R p).toRingEquiv
    (algebraMap R (Localization.AtPrime p.asIdeal) a)
  change Ring.ord ((Spec (.of R)).presheaf.stalk p)
    ((StructureSheaf.stalkIso R p) (algebraMap R (Localization.AtPrime p.asIdeal) a)) = _ at he
  rw [helem] at he
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) he

theorem affine_field_order (R L : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (p : Spec (.of R)) (hp : p.asIdeal.height = 1) (a : R) (ha : a ≠ 0) :
    (Spec (.of R)).ord ((FractionField.fieldIso R L).inv (algebraMap R L a)) p =
      ((Ring.ord (Localization.AtPrime p.asIdeal)
        (algebraMap R (Localization.AtPrime p.asIdeal) a)).toNat : ℤ) := by
  have he : (FractionField.fieldIso R L).inv (algebraMap R L a) =
      StructureSheaf.toStalk R (genericPoint (Spec (.of R))) a := by
    apply (FractionField.fieldIso R L).commRingCatIsoToRingEquiv.injective
    exact ((FractionField.fieldIso R L).commRingCatIsoToRingEquiv.apply_symm_apply _).trans
      (congrArg (fun t : CommRingCat.of R ⟶ CommRingCat.of L => t a)
        (FractionField.toStalk_fieldIso R L)).symm
  rw [he]
  exact affine_order R p hp a ha

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalOrder
