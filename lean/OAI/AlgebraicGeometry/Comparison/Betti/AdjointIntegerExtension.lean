import OAI.AlgebraicGeometry.Comparison.Betti.ImageExtensionSquare

/-! # Adjoint Integer Extension -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdjointIntegerExtension

noncomputable section

/-! The actual inverse-image adjoint commutes with the canonical extension from nonnegative to integer degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X Y : TopCat.{0}} (f : Y ⟶ X)
  {K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ} {L : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℕ}
  (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L)

def nonnegativeDirectImageAdjointComplexMap :
    ((TopologicalSheafPullback.sheafInverseImage f).mapHomologicalComplex (.up ℕ)).obj K ⟶ L :=
  ((Complex.Adjunction.onComplexes (TopologicalSheafPullback.sheafImageAdjunction f) (.up ℕ)).homEquiv K L).symm α

theorem directImageAdjointComplexMap_extend :
    ImageAdjointNaturality.directImageAdjointComplexMap f (ImageExtensionSquare.extendDirectImageComplexMap f α) =
      (Complex.Extension.mapExtendIso (TopologicalSheafPullback.sheafInverseImage f)
        (ComplexShape.embeddingUpIntGE 0) K).hom ≫
      HomologicalComplex.extendMap (nonnegativeDirectImageAdjointComplexMap f α)
        (ComplexShape.embeddingUpIntGE 0) := by
  apply HomologicalComplex.Hom.ext
  funext i
  change ((TopologicalSheafPullback.sheafImageAdjunction f).homEquiv
      (HomologicalComplex.extend.X K ((ComplexShape.embeddingUpIntGE 0).r i))
      (HomologicalComplex.extend.X L ((ComplexShape.embeddingUpIntGE 0).r i))).symm
      (HomologicalComplex.extend.mapX α ((ComplexShape.embeddingUpIntGE 0).r i) ≫
        (Complex.Extension.mapXIso (TopologicalSheafPullback.sheafDirectImage f) L ((ComplexShape.embeddingUpIntGE 0).r i)).inv) =
    (Complex.Extension.mapXIso (TopologicalSheafPullback.sheafInverseImage f) K ((ComplexShape.embeddingUpIntGE 0).r i)).hom ≫
      HomologicalComplex.extend.mapX (nonnegativeDirectImageAdjointComplexMap f α)
        ((ComplexShape.embeddingUpIntGE 0).r i)
  generalize (ComplexShape.embeddingUpIntGE 0).r i = o
  cases o with
  | none => exact ((TopologicalSheafPullback.sheafInverseImage f).map_isZero (isZero_zero (ConstantSheafSections.ComplexSheaves X))).eq_of_src _ _
  | some n =>
    change ((TopologicalSheafPullback.sheafImageAdjunction f).homEquiv (K.X n) (L.X n)).symm (α.f n ≫ 𝟙 _) =
      𝟙 _ ≫ ((TopologicalSheafPullback.sheafImageAdjunction f).homEquiv (K.X n) (L.X n)).symm (α.f n)
    erw [Category.comp_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.Comparison.Betti.AdjointIntegerExtension
