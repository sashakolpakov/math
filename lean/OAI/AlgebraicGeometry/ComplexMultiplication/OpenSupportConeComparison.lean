import OAI.AlgebraicGeometry.ComplexMultiplication.OpenSupportUnitCone
import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalKernelConeHomology
import OAI.AlgebraicTopology.Support.SectionRestrictionConeNaturality
import OAI.Algebra.Homology.MappingConeMapNaturality

/-! # Open Support Cone Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.OpenSupportConeComparison

noncomputable section

/-! # The supported unit is the literal original sheafification cone map -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf

@[reassoc]
private theorem cochainIso_hom_inv_f {C : Type*} [Category* C] [HasZeroMorphisms C]
    {K L : CochainComplex C ℤ} (e : K ≅ L) (n : ℤ) :
    e.hom.f n ≫ e.inv.f n = 𝟙 (K.X n) := by
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
    congrArg (fun f : K ⟶ K => f.f n) e.hom_inv_id

@[reassoc]
private theorem cochainIso_inv_hom_f {C : Type*} [Category* C] [HasZeroMorphisms C]
    {K L : CochainComplex C ℤ} (e : K ≅ L) (n : ℤ) :
    e.inv.f n ≫ e.hom.f n = 𝟙 (L.X n) := by
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
    congrArg (fun f : L ⟶ L => f.f n) e.inv_hom_id

variable (Y : TopCat.{0}) [T2Space Y] [∀ W : Opens Y, ParacompactSpace W]
  (U V : Opens Y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison uses the original raw cochain unit on both entries of the cone. -/
theorem originalOpenSupportUnitCone_raw :
    (AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeIsoRelative ℚ Y (Opens.infLELeft V U)).hom ≫
      OpenSupportUnitCone.originalOpenSupportUnitCone Y U V ≫
      (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestrictionExtendConeIso Y
        (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℚ Y) (Opens.infLELeft V U)).hom =
    AlgebraicTopology.Singular.SheafCochainOpenCone.openRawToSingularSheafRestrictionCone ℚ Y (Opens.infLELeft V U) := by
  have hraw : (AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeIsoRelative ℚ Y
      (Opens.infLELeft V U)).hom =
    CochainComplex.mappingCone.map _ _
      (AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularCochainComplexIntIsoDual ℚ Y V).hom
      (AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularCochainComplexIntIsoDual ℚ Y (V ⊓ U)).hom
      (AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionInt_transport ℚ Y (Opens.infLELeft V U)) :=
    Algebra.Homology.MappingConeMapNaturality.CochainComplex.mappingCone.mapArrowHom_eq_map _ _ _ _ _
  have hext : (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestrictionExtendConeIso Y
      (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℚ Y) (Opens.infLELeft V U)).hom =
    CochainComplex.mappingCone.map _ _
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y V)
        (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℚ Y) ComplexShape.embeddingUpNat).hom
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y (V ⊓ U))
        (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℚ Y) ComplexShape.embeddingUpNat).hom
      (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction_extend Y (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℚ Y)
        (Opens.infLELeft V U)) :=
    Algebra.Homology.MappingConeMapNaturality.CochainComplex.mappingCone.mapArrowHom_eq_map _ _ _ _ _
  rw [hraw, hext]
  dsimp only [OpenSupportUnitCone.originalOpenSupportUnitCone]
  rw [AlgebraicTopology.Support.SectionRestrictionConeNaturality.TopCat.Sheaf.supportRestrictionSectionsConeIso_hom]
  ext n : 1
  apply CochainComplex.mappingCone.ext_from _ (n + 1) n rfl
  all_goals
    simp only [SupportedOpenUnit.originalOpenRelativeShortComplex, SupportedOpenUnit.originalOpenSupportShortComplex,
      AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt, AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexNat,
      ShortComplex.map, AlgebraicTopology.Singular.RelativeCochainCone.relativeCochainRestrictionInt, ComplexShape.Embedding.extendFunctor_map,
      AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex,
      HomologicalComplex.comp_f, Category.assoc,
      AlgebraicTopology.Singular.SheafCochainOpenCone.openRawToSingularSheafRestrictionCone, CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.mappingCone.inr_f_desc_f,
      CochainComplex.mappingCone.inr_f_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v,
      SupportedOpenUnit.originalOpenSupportUnit, SupportedOpenUnit.originalOpenSupportUnitAmbient,
      SupportedOpenUnit.originalOpenSupportUnitComplement, SupportedOpenUnit.originalOpenDualToIntegerSections,
      SupportedOpenUnit.originalOpenRawToIntegerSections, HomologicalComplex.comp_f,
      HomologicalComplex.id_f, Category.assoc]
  all_goals
    simp only [cochainIso_hom_inv_f_assoc, cochainIso_inv_hom_f_assoc, Category.id_comp]
  all_goals rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.OpenSupportConeComparison
