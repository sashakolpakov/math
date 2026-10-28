import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationStalks
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FractionField

/-! # Normalization Stalk Fields -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationStalkFields

noncomputable section

/-! The actual localized relative-normalization map preserves the chosen
extension-field coordinates on rational functions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.Normalization OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationFields
  NormalizationCharts NormalizationStalks

attribute [local instance] NormalizationStalks.sectionAlgebra NormalizationStalks.stalkAlgebra

universe u

variable (Y : Scheme.{u}) [IsIntegral Y] (L : Type u) [Field L] [Algebra Y.functionField L]
  (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] (y : U)

theorem chartGenericMap_comp :
    Spec.map (CommRingCat.ofHom (algebraMap (integralClosure Γ(Y, U) L) L)) ≫
      NormalizationCharts.chartMap Y L U hU = NormalizationFields.toRelativeNormalization Y L := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (NormalizationFields.toRelativeNormalization Y L)
    (hU.preimage (Normalization.relativeNormalizationMap Y L)) (isAffineOpen_top _)
    (NormalizationFields.toRelativeNormalization_preimage Y L U).ge
  rw [IsAffineOpen.fromSpec_top, Iso.eq_inv_comp, Scheme.isoSpec_Spec_hom] at h
  rw [NormalizationCharts.chartMap, ← Spec.map_comp_assoc, ← NormalizationFields.toRelativeNormalization_app Y L U hU]
  simpa only [Spec.map_comp_assoc] using h

theorem stalkGenericMap_comp :
    Spec.map (CommRingCat.ofHom (algebraMap (integralClosure (Y.presheaf.stalk y) L) L)) ≫
      NormalizationStalks.stalkMap Y L U hU y = NormalizationFields.toRelativeNormalization Y L := by
  rw [NormalizationStalks.stalkMap, ← Spec.map_comp_assoc]
  exact chartGenericMap_comp Y L U hU

def stalkFieldMap : (Normalization.relativeNormalization Y L).functionField ⟶
    (Spec (.of (integralClosure (Y.presheaf.stalk y) L))).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (NormalizationStalks.stalkMap Y L U hU y) (NormalizationStalks.stalkMap_genericPoint Y L U hU y)

instance : IsIso (stalkFieldMap Y L U hU y) := by
  let := NormalizationStalks.stalkMap_stalkMap_isIso Y L U hU y
    (genericPoint (Spec (.of (integralClosure (Y.presheaf.stalk y) L))))
  unfold stalkFieldMap Cycles.Functoriality.FunctionFields.Construction.genericFieldMap
  infer_instance

variable [Module.Finite Y.functionField L]

/-- Local and global rational functions have exactly the same image in
the specified extension field. -/
theorem stalkFieldMap_square :
    letI : IsFractionRing (integralClosure (Y.presheaf.stalk y) L) L :=
      integralClosure.isFractionRing_of_finite_extension Y.functionField L
    stalkFieldMap Y L U hU y ≫
      (Affine.FractionField.fieldIso (integralClosure (Y.presheaf.stalk y) L) L).hom =
        (NormalizationFields.relativeFunctionFieldIso Y L).hom := by
  let D := integralClosure (Y.presheaf.stalk y) L
  let : IsFractionRing D L := integralClosure.isFractionRing_of_finite_extension Y.functionField L
  have h := Generic.Fields.genericFieldMap_comp
    (Spec.map (CommRingCat.ofHom (algebraMap D L))) (NormalizationStalks.stalkMap Y L U hU y)
    (Affine.FractionField.genericMap_genericPoint D L) (NormalizationStalks.stalkMap_genericPoint Y L U hU y)
  have hc := Generic.Fields.genericFieldMap_congr (stalkGenericMap_comp Y L U hU y)
    ((congrArg (NormalizationStalks.stalkMap Y L U hU y) (Affine.FractionField.genericMap_genericPoint D L)).trans
      (NormalizationStalks.stalkMap_genericPoint Y L U hU y)) (NormalizationFields.toRelativeNormalization_genericPoint Y L)
  rw [hc, Affine.FractionField.genericMap_fieldMap] at h
  have he := congrArg (fun t : (Normalization.relativeNormalization Y L).functionField ⟶
      (Spec (.of L)).functionField => t ≫ (SpecField.fieldIso L).inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at he
  ext a
  exact congrArg (fun t : (Normalization.relativeNormalization Y L).functionField ⟶ CommRingCat.of L => t a) he.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationStalkFields
