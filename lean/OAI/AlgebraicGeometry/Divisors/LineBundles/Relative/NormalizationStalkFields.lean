import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationStalks
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.FractionField

/-! # Normalization Stalk Fields -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationStalkFields.BundleCycles.RelativeNormalizationStalkFields

noncomputable section

/-! The actual localized relative-normalization map preserves the chosen
extension-field coordinates on rational functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.Normalization.BundleCycles.RelativeNormalization OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields
  NormalizationCharts.BundleCycles.RelativeNormalizationCharts NormalizationStalks.BundleCycles.RelativeNormalizationStalks

attribute [local instance] NormalizationStalks.BundleCycles.RelativeNormalizationStalks.sectionAlgebra NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkAlgebra

universe u

variable (Y : Scheme.{u}) [IsIntegral Y] (L : Type u) [Field L] [Algebra Y.functionField L]
  (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] (y : U)

theorem chartGenericMap_comp :
    Spec.map (CommRingCat.ofHom (algebraMap (integralClosure Γ(Y, U) L) L)) ≫
      NormalizationCharts.BundleCycles.RelativeNormalizationCharts.chartMap Y L U hU = NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization Y L := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization Y L)
    (hU.preimage (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)) (isAffineOpen_top _)
    (NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization_preimage Y L U).ge
  rw [IsAffineOpen.fromSpec_top, Iso.eq_inv_comp, Scheme.isoSpec_Spec_hom] at h
  rw [NormalizationCharts.BundleCycles.RelativeNormalizationCharts.chartMap, ← Spec.map_comp_assoc, ← NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization_app Y L U hU]
  simpa only [Spec.map_comp_assoc] using h

theorem stalkGenericMap_comp :
    Spec.map (CommRingCat.ofHom (algebraMap (integralClosure (Y.presheaf.stalk y) L) L)) ≫
      NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap Y L U hU y = NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization Y L := by
  rw [NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap, ← Spec.map_comp_assoc]
  exact chartGenericMap_comp Y L U hU

def stalkFieldMap : (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).functionField ⟶
    (Spec (.of (integralClosure (Y.presheaf.stalk y) L))).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap Y L U hU y) (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap_genericPoint Y L U hU y)

instance : IsIso (stalkFieldMap Y L U hU y) := by
  let := NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap_stalkMap_isIso Y L U hU y
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
      (Affine.FractionField.BundleCycles.AffineFractionField.fieldIso (integralClosure (Y.presheaf.stalk y) L) L).hom =
        (NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeFunctionFieldIso Y L).hom := by
  let D := integralClosure (Y.presheaf.stalk y) L
  let : IsFractionRing D L := integralClosure.isFractionRing_of_finite_extension Y.functionField L
  have h := GenericFieldComposition.BundleCycles.genericFieldMap_comp
    (Spec.map (CommRingCat.ofHom (algebraMap D L))) (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap Y L U hU y)
    (Affine.FractionField.BundleCycles.AffineFractionField.genericMap_genericPoint D L) (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap_genericPoint Y L U hU y)
  have hc := GenericFieldComposition.BundleCycles.genericFieldMap_congr (stalkGenericMap_comp Y L U hU y)
    ((congrArg (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap Y L U hU y) (Affine.FractionField.BundleCycles.AffineFractionField.genericMap_genericPoint D L)).trans
      (NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkMap_genericPoint Y L U hU y)) (NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization_genericPoint Y L)
  rw [hc, Affine.FractionField.BundleCycles.AffineFractionField.genericMap_fieldMap] at h
  have he := congrArg (fun t : (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).functionField ⟶
      (Spec (.of L)).functionField => t ≫ (SpecFieldOf.BundleCycles.SpecField.fieldIso L).inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at he
  ext a
  exact congrArg (fun t : (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).functionField ⟶ CommRingCat.of L => t a) he.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationStalkFields.BundleCycles.RelativeNormalizationStalkFields
