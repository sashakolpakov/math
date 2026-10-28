import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationStalkFields

/-! # Normalization Norm -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationNorm.BundleCycles.RelativeNormalizationNorm

noncomputable section

/-! The native function-field embedding of the finite relative
normalization agrees with the specified extension, including its norm. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.Normalization.BundleCycles.RelativeNormalization OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationLocal.BundleCycles.RelativeNormalizationLocal OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields
  NormalizationStalks.BundleCycles.RelativeNormalizationStalks

attribute [local instance] NormalizationStalks.BundleCycles.RelativeNormalizationStalks.sectionAlgebra NormalizationStalks.BundleCycles.RelativeNormalizationStalks.stalkAlgebra

universe u

variable (Y : Scheme.{u}) [IsIntegral Y] (L : Type u) [Field L]
  [Algebra Y.functionField L] [Module.Finite Y.functionField L]

theorem relativeFunctionFieldIso_germ (U : Y.Opens) (hU : IsAffineOpen U)
    [Nonempty U] [Nonempty (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ⁻¹ᵁ U)] :
    (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).germToFunctionField (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ⁻¹ᵁ U) ≫
      (NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeFunctionFieldIso Y L).hom =
        (NormalizationLocal.BundleCycles.RelativeNormalizationLocal.affineRingIso Y L U hU).hom ≫
          CommRingCat.ofHom (algebraMap (integralClosure Γ(Y, U) L) L) := by
  let : Nonempty (⊤ : (Spec (.of L)).Opens) := ⟨⟨genericPoint _, trivial⟩⟩
  have h := GenericFieldComposition.BundleCycles.genericFieldMap_germ_appLE (NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization Y L)
    (NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization_genericPoint Y L) (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ⁻¹ᵁ U) ⊤
    (NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization_preimage Y L U).ge
  rw [← SpecFieldOf.BundleCycles.SpecField.fieldIso_germ, ← Category.assoc, NormalizationFields.BundleCycles.RelativeNormalizationFields.toRelativeNormalization_app Y L U hU] at h
  have hc := congrArg (fun t : Γ(Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L, Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ⁻¹ᵁ U) ⟶
      (Spec (.of L)).functionField => t ≫ (SpecFieldOf.BundleCycles.SpecField.fieldIso L).inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hc
  ext a
  exact congrArg (fun t : Γ(Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L, Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ⁻¹ᵁ U) ⟶
    CommRingCat.of L => t a) hc

theorem relativeFieldMap_square :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L) (NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeNormalizationMap_genericPoint Y L) ≫
      (NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeFunctionFieldIso Y L).hom = CommRingCat.ofHom (algebraMap Y.functionField L) := by
  let y := genericPoint Y
  let U : Y.Opens := (Y.affineCover.f (Y.affineCover.idx y)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (Y.affineCover.f _)
  let : Nonempty U := ⟨⟨y, Y.affineCover.covers y⟩⟩
  let : Nonempty (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L ⁻¹ᵁ U) :=
    ⟨⟨genericPoint (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L), by
      change Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L (genericPoint (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L)) ∈ U
      rw [NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeNormalizationMap_genericPoint]
      exact Y.affineCover.covers y⟩⟩
  let := functionField_isFractionRing_of_isAffineOpen Y U hU
  have hg : Y.germToFunctionField U ≫
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L) (NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeNormalizationMap_genericPoint Y L) ≫
        (NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeFunctionFieldIso Y L).hom =
      Y.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap Y.functionField L) := by
    rw [← Category.assoc, Deformation.FunctionField.BundleCycles.genericFieldMap_germOn, Category.assoc,
      relativeFunctionFieldIso_germ Y L U hU, ← Category.assoc, NormalizationLocal.BundleCycles.RelativeNormalizationLocal.affineRingIso_base]
    rfl
  apply CommRingCat.hom_ext
  apply IsFractionRing.ringHom_ext (A := Γ(Y, U))
  intro a
  exact congrArg (fun t : Γ(Y, U) ⟶ CommRingCat.of L => t a) hg

/-- The norm defined by the actual generic-stalk map is exactly the norm
in the chosen finite extension. -/
theorem relativeFieldMap_norm (g : (Normalization.BundleCycles.RelativeNormalization.relativeNormalization Y L).functionField) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)
      (NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeNormalizationMap_genericPoint Y L)).hom.toAlgebra
    Algebra.norm Y.functionField g = Algebra.norm Y.functionField ((NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeFunctionFieldIso Y L).hom g) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap Y L)
    (NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeNormalizationMap_genericPoint Y L)).hom.toAlgebra
  exact Algebra.norm_eq_of_equiv_equiv (RingEquiv.refl Y.functionField)
    (NormalizationFields.BundleCycles.RelativeNormalizationFields.relativeFunctionFieldIso Y L).commRingCatIsoToRingEquiv
    (congrArg CommRingCat.Hom.hom (relativeFieldMap_square Y L).symm) g

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationNorm.BundleCycles.RelativeNormalizationNorm
