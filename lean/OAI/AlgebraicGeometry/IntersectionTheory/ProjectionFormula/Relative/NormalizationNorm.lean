import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationStalkFields

/-! # Normalization Norm -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationNorm

noncomputable section

/-! The native function-field embedding of the finite relative
normalization agrees with the specified extension, including its norm. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.Normalization OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationLocal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationFields
  NormalizationStalks

attribute [local instance] NormalizationStalks.sectionAlgebra NormalizationStalks.stalkAlgebra

universe u

variable (Y : Scheme.{u}) [IsIntegral Y] (L : Type u) [Field L]
  [Algebra Y.functionField L] [Module.Finite Y.functionField L]

theorem relativeFunctionFieldIso_germ (U : Y.Opens) (hU : IsAffineOpen U)
    [Nonempty U] [Nonempty (Normalization.relativeNormalizationMap Y L ⁻¹ᵁ U)] :
    (Normalization.relativeNormalization Y L).germToFunctionField (Normalization.relativeNormalizationMap Y L ⁻¹ᵁ U) ≫
      (NormalizationFields.relativeFunctionFieldIso Y L).hom =
        (NormalizationLocal.affineRingIso Y L U hU).hom ≫
          CommRingCat.ofHom (algebraMap (integralClosure Γ(Y, U) L) L) := by
  let : Nonempty (⊤ : (Spec (.of L)).Opens) := ⟨⟨genericPoint _, trivial⟩⟩
  have h := Generic.Fields.genericFieldMap_germ_appLE (NormalizationFields.toRelativeNormalization Y L)
    (NormalizationFields.toRelativeNormalization_genericPoint Y L) (Normalization.relativeNormalizationMap Y L ⁻¹ᵁ U) ⊤
    (NormalizationFields.toRelativeNormalization_preimage Y L U).ge
  rw [← SpecField.fieldIso_germ, ← Category.assoc, NormalizationFields.toRelativeNormalization_app Y L U hU] at h
  have hc := congrArg (fun t : Γ(Normalization.relativeNormalization Y L, Normalization.relativeNormalizationMap Y L ⁻¹ᵁ U) ⟶
      (Spec (.of L)).functionField => t ≫ (SpecField.fieldIso L).inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hc
  ext a
  exact congrArg (fun t : Γ(Normalization.relativeNormalization Y L, Normalization.relativeNormalizationMap Y L ⁻¹ᵁ U) ⟶
    CommRingCat.of L => t a) hc

theorem relativeFieldMap_square :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.relativeNormalizationMap Y L) (NormalizationFields.relativeNormalizationMap_genericPoint Y L) ≫
      (NormalizationFields.relativeFunctionFieldIso Y L).hom = CommRingCat.ofHom (algebraMap Y.functionField L) := by
  let y := genericPoint Y
  let U : Y.Opens := (Y.affineCover.f (Y.affineCover.idx y)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (Y.affineCover.f _)
  let : Nonempty U := ⟨⟨y, Y.affineCover.covers y⟩⟩
  let : Nonempty (Normalization.relativeNormalizationMap Y L ⁻¹ᵁ U) :=
    ⟨⟨genericPoint (Normalization.relativeNormalization Y L), by
      change Normalization.relativeNormalizationMap Y L (genericPoint (Normalization.relativeNormalization Y L)) ∈ U
      rw [NormalizationFields.relativeNormalizationMap_genericPoint]
      exact Y.affineCover.covers y⟩⟩
  let := functionField_isFractionRing_of_isAffineOpen Y U hU
  have hg : Y.germToFunctionField U ≫
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.relativeNormalizationMap Y L) (NormalizationFields.relativeNormalizationMap_genericPoint Y L) ≫
        (NormalizationFields.relativeFunctionFieldIso Y L).hom =
      Y.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap Y.functionField L) := by
    rw [← Category.assoc, Generic.Fields.genericFieldMap_germ_open, Category.assoc,
      relativeFunctionFieldIso_germ Y L U hU, ← Category.assoc, NormalizationLocal.affineRingIso_base]
    rfl
  apply CommRingCat.hom_ext
  apply IsFractionRing.ringHom_ext (A := Γ(Y, U))
  intro a
  exact congrArg (fun t : Γ(Y, U) ⟶ CommRingCat.of L => t a) hg

/-- The norm defined by the actual generic-stalk map is exactly the norm
in the chosen finite extension. -/
theorem relativeFieldMap_norm (g : (Normalization.relativeNormalization Y L).functionField) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.relativeNormalizationMap Y L)
      (NormalizationFields.relativeNormalizationMap_genericPoint Y L)).hom.toAlgebra
    Algebra.norm Y.functionField g = Algebra.norm Y.functionField ((NormalizationFields.relativeFunctionFieldIso Y L).hom g) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Normalization.relativeNormalizationMap Y L)
    (NormalizationFields.relativeNormalizationMap_genericPoint Y L)).hom.toAlgebra
  exact Algebra.norm_eq_of_equiv_equiv (RingEquiv.refl Y.functionField)
    (NormalizationFields.relativeFunctionFieldIso Y L).commRingCatIsoToRingEquiv
    (congrArg CommRingCat.Hom.hom (relativeFieldMap_square Y L).symm) g

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationNorm
