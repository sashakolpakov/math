import OAI.AlgebraicGeometry.ComplexMultiplication.OpenSupportUnitForget
import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSheafComparison

/-! # Open Global Singular Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.OpenGlobalSingularNormalization

noncomputable section

/-! # The top-open singular unit is the canonical ordinary cohomology comparison -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.HomologicalComplex
open _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf

theorem originalOpenTopUnit_eq (Y : TopCat.{0}) :
    AlgebraicTopology.Singular.SheafCochainOpenSections.openRawToSingularCochainSheafComplex ℚ Y ⊤ =
      AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℚ Y := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [AlgebraicTopology.Singular.GlobalRestriction.topOpenToGlobalSingularCochainSheafComplex_f]
  rfl

theorem originalTopEvaluation_extendIso (Y : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℕ) :
    Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso
        (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y) K
        ComplexShape.embeddingUpNat =
      Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y ⊤) K
        ComplexShape.embeddingUpNat := rfl

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

omit [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] in
theorem originalOpenRawGlobalInteger_normalization (n : ℕ)
    (a : ((AlgebraicTopology.Singular.SheafCochainOpenSections.openRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⊤).extend
      ComplexShape.embeddingUpNat).homology (n : ℤ)) :
    (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso ℚ X n).hom
      (homologyMap (SupportedOpenUnit.originalOpenRawToIntegerSections (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⊤)
        (n : ℤ) a) =
    homologyMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℚ
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) n
      ((AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).extendHomologyIso
        ComplexShape.embeddingUpNat rfl |>.hom a) := by
  let Y := TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)
  let unit := AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℚ Y
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.extendHomologyIso_hom_naturality unit
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl) a
  dsimp only [Coefficient.SheafComparison.singularGlobalIntegerHomologyIso, SupportedOpenUnit.originalOpenRawToIntegerSections,
    Iso.trans_hom, HomologicalComplex.homologyMapIso_hom]
  rw [originalTopEvaluation_extendIso, originalOpenTopUnit_eq]
  simp only [HomologicalComplex.homologyMap_comp, AddCommGrpCat.comp_apply]
  let e := homologyMapIso (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso
    (AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y ⊤) (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℚ Y)
      ComplexShape.embeddingUpNat) (n : ℤ)
  change ((AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex ℚ Y).extendHomologyIso
      ComplexShape.embeddingUpNat rfl).hom
        (e.hom (e.inv (homologyMap (extendMap unit ComplexShape.embeddingUpNat) (n : ℤ) a))) = _
  have he : e.hom (e.inv (homologyMap (extendMap unit ComplexShape.embeddingUpNat)
      (n : ℤ) a)) = homologyMap (extendMap unit ComplexShape.embeddingUpNat) (n : ℤ) a :=
    ConcreteCategory.congr_hom e.inv_hom_id _
  rw [he]
  simpa only [HomologicalComplex.homologyMap_comp, AddCommGrpCat.comp_apply] using! h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.OpenGlobalSingularNormalization
