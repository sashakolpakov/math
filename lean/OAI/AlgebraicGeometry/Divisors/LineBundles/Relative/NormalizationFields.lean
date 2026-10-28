import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationLocal
import OAI.AlgebraicGeometry.Divisors.LineBundles.SpecFieldOf

/-! # Normalization Fields -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields

noncomputable section

/-! The actual function field of the relative normalization is the chosen
finite extension. The identification is induced by its generic map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.Normalization.BundleCycles.RelativeNormalization OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationLocal.BundleCycles.RelativeNormalizationLocal

universe u

variable (Y : Scheme.{u}) [IsIntegral Y] (L : Type u) [Field L] [Algebra Y.functionField L]

def toRelativeNormalization : Spec (.of L) ⟶ Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L :=
  (Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L).toNormalization

instance : IsDominant (toRelativeNormalization Y L) := by
  exact inferInstanceAs (IsDominant (Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L).toNormalization)

theorem toRelativeNormalization_comp :
    toRelativeNormalization Y L ≫ Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L = Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L :=
  (Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L).toNormalization_fromNormalization

theorem toRelativeNormalization_genericPoint :
    toRelativeNormalization Y L (genericPoint (Spec (.of L))) =
      genericPoint (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L) := by
  apply IsGenericPoint.eq _ (genericPoint_spec _)
  have h := (genericPoint_spec (Spec (.of L))).image (toRelativeNormalization Y L).continuous
  simpa only [Set.image_univ, (toRelativeNormalization Y L).denseRange.closure_range] using h

theorem toRelativeNormalization_preimage (U : Y.Opens) [Nonempty U] :
    toRelativeNormalization Y L ⁻¹ᵁ (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ⁻¹ᵁ U) = ⊤ := by
  rw [← Scheme.Hom.comp_preimage, toRelativeNormalization_comp, Normalization.BundleCycles.RelativeNormalization.fieldGenericMap_preimage]

theorem relativeNormalizationMap_genericPoint :
    Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L (genericPoint (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L)) = genericPoint Y := by
  rw [← toRelativeNormalization_genericPoint]
  change (toRelativeNormalization Y L ≫ Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L) _ = _
  rw [toRelativeNormalization_comp, Normalization.BundleCycles.RelativeNormalization.fieldGenericMap_apply]

local instance (U : Y.Opens) [Nonempty U] : Algebra Γ(Y, U) L :=
  ((algebraMap Y.functionField L).comp (algebraMap Γ(Y, U) Y.functionField)).toAlgebra

local instance (U : Y.Opens) [Nonempty U] : IsScalarTower Γ(Y, U) Y.functionField L :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem toRelativeNormalization_app (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (toRelativeNormalization Y L).appLE (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ⁻¹ᵁ U) ⊤
        (toRelativeNormalization_preimage Y L U).ge ≫ (Scheme.ΓSpecIso (.of L)).hom =
      (NormalizationLocal.BundleCycles.RelativeNormalizationLocal.affineRingIso Y L U hU).hom ≫
        CommRingCat.ofHom (algebraMap (integralClosure Γ(Y, U) L) L) := by
  let := ((Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L).app U).hom.toAlgebra
  have h := (Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L).normalizationObjIso_hom_val hU
  have hs : (NormalizationLocal.BundleCycles.RelativeNormalizationLocal.affineRingIso Y L U hU).hom ≫
      CommRingCat.ofHom (algebraMap (integralClosure Γ(Y, U) L) L) =
      (Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L).toNormalization.appLE
        ((Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L).fromNormalization ⁻¹ᵁ U) (Normalization.BundleCycles.RelativeNormalization.fieldGenericMap Y L ⁻¹ᵁ U)
        (by rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]) ≫
          (Normalization.BundleCycles.RelativeNormalization.preimageFieldIso Y L U).hom := by
    rw [← h]
    rfl
  rw [hs]
  simp only [Normalization.BundleCycles.RelativeNormalization.preimageFieldIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
    Scheme.Hom.appLE_map_assoc]
  rfl

variable [Module.Finite Y.functionField L]

theorem toRelativeNormalization_fieldMap_bijective :
    Function.Bijective (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (toRelativeNormalization Y L)
      (toRelativeNormalization_genericPoint Y L)) := by
  let y := genericPoint Y
  let U : Y.Opens := (Y.affineCover.f (Y.affineCover.idx y)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (Y.affineCover.f _)
  let : Nonempty U := ⟨⟨y, Y.affineCover.covers y⟩⟩
  let V : (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).Opens := Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ⁻¹ᵁ U
  let : Nonempty V := ⟨⟨toRelativeNormalization Y L (genericPoint (Spec (.of L))), by
    change Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L (toRelativeNormalization Y L _) ∈ U
    rw [← Scheme.Hom.comp_apply, toRelativeNormalization_comp, Normalization.BundleCycles.RelativeNormalization.fieldGenericMap_apply]
    exact Y.affineCover.covers y⟩⟩
  let := functionField_isFractionRing_of_isAffineOpen Y U hU
  let : IsFractionRing (integralClosure Γ(Y, U) L) L :=
    integralClosure.isFractionRing_of_finite_extension Y.functionField L
  exact SpecFieldOf.BundleCycles.SpecField.genericFieldMap_bijective_of_chart L (toRelativeNormalization Y L)
    (toRelativeNormalization_genericPoint Y L) V (toRelativeNormalization_preimage Y L U).ge
    (integralClosure Γ(Y, U) L) (NormalizationLocal.BundleCycles.RelativeNormalizationLocal.affineRingIso Y L U hU)
    (toRelativeNormalization_app Y L U hU)

def relativeFunctionFieldIso : (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).functionField ≅ CommRingCat.of L :=
  (RingEquiv.ofBijective
    (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (toRelativeNormalization Y L)
      (toRelativeNormalization_genericPoint Y L)).hom
    (toRelativeNormalization_fieldMap_bijective Y L)).toCommRingCatIso ≪≫
      (SpecFieldOf.BundleCycles.SpecField.fieldIso L).symm

instance toRelativeNormalization_fieldMap_isIso :
    IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (toRelativeNormalization Y L)
      (toRelativeNormalization_genericPoint Y L)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (toRelativeNormalization_fieldMap_bijective Y L)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields
