import OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericUniversalHomogeneity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneityLineBaseChange

/-! # Generic Homogeneity Naturality -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericHomogeneityNaturality.Geometric.GenericHomogeneity

noncomputable section

/-! Both actual line bundles detecting homogeneity commute with
parameter change, through their original line-bundle classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneityLineBaseChange

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {P T : Over S}
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left) (u : T ⟶ P)

theorem universalParameterLine_class_naturality :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((u ⊗ₘ 𝟙 A.scheme) ⊗ₘ 𝟙 A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (GenericUniversalHomogeneity.Geometric.GenericHomogeneity.universalParameterLine A Q)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (GenericUniversalHomogeneity.Geometric.GenericHomogeneity.universalParameterLine A (Q.pullback (u ⊗ₘ 𝟙 A.scheme).left)) := by
  have hf : (u ⊗ₘ 𝟙 A.scheme) ≫ fst P A.scheme = fst T A.scheme ≫ u := by simp
  exact (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass_naturality Q (fst P A.scheme) (u ⊗ₘ 𝟙 A.scheme)).trans
    ((congrArg (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q) hf).trans (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass_baseChange Q u (fst T A.scheme)))

theorem universalTranslationLine_class_naturality :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((u ⊗ₘ 𝟙 A.scheme) ⊗ₘ 𝟙 A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (GenericUniversalHomogeneity.Geometric.GenericHomogeneity.universalTranslationLine A Q)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (GenericUniversalHomogeneity.Geometric.GenericHomogeneity.universalTranslationLine A (Q.pullback (u ⊗ₘ 𝟙 A.scheme).left)) := by
  have hs : (u ⊗ₘ 𝟙 A.scheme) ≫ snd P A.scheme = snd T A.scheme := by simp
  have h := A.translationClass_naturality (u ⊗ₘ 𝟙 A.scheme) (snd P A.scheme)
    (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q (fst P A.scheme))
  exact h.trans (congrArg₂ (fun a q => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left q)
    hs (universalParameterLine_class_naturality A Q u))

theorem normalizedUniversalParameterLine_class_naturality :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((u ⊗ₘ 𝟙 A.scheme) ⊗ₘ 𝟙 A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (GenericUniversalHomogeneity.Geometric.GenericHomogeneity.normalizedUniversalParameterLine A Q)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (GenericUniversalHomogeneity.Geometric.GenericHomogeneity.normalizedUniversalParameterLine A (Q.pullback (u ⊗ₘ 𝟙 A.scheme).left)) :=
  AbelianModuli.ReferenceFamily.HomogeneityLineBaseChange.normalizedProductBundle_pullbackClass A.scheme (u ⊗ₘ 𝟙 A.scheme) _ _
    (universalParameterLine_class_naturality A Q u)

theorem normalizedUniversalTranslationLine_class_naturality :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((u ⊗ₘ 𝟙 A.scheme) ⊗ₘ 𝟙 A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (GenericUniversalHomogeneity.Geometric.GenericHomogeneity.normalizedUniversalTranslationLine A Q)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (GenericUniversalHomogeneity.Geometric.GenericHomogeneity.normalizedUniversalTranslationLine A (Q.pullback (u ⊗ₘ 𝟙 A.scheme).left)) :=
  AbelianModuli.ReferenceFamily.HomogeneityLineBaseChange.normalizedProductBundle_pullbackClass A.scheme (u ⊗ₘ 𝟙 A.scheme) _ _
    (universalTranslationLine_class_naturality A Q u)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericHomogeneityNaturality.Geometric.GenericHomogeneity
