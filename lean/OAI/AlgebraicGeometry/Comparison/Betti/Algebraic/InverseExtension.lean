import OAI.AlgebraicGeometry.Comparison.Betti.AdjointIntegerExtension
import OAI.AlgebraicGeometry.Comparison.Betti.ImageAdjointNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.ExtensionNaturality

/-! # Inverse Extension -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.InverseExtension

noncomputable section

/-! The canonical integer extension retains the actual algebraic inverse-image coefficient map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

theorem algebraicDirectImage_extension_square :
    (Analytic.De.algebraicSheafIntExtensionIso Y).hom ≫
        ImageExtensionSquare.extendDirectImageComplexMap f.left.base (Sheaf.CochainPullback.deRhamSheafDirectImage f) =
      OpenForms.deRhamSheafDirectImageInt f ≫
        ((Sheaves.directImage f).mapHomologicalComplex (.up ℤ)).map (Analytic.De.algebraicSheafIntExtensionIso X).hom := by
  let e := Complex.Extension.mapExtendIso (Sheaves.directImage f) (ComplexShape.embeddingUpIntGE 0)
    (Sheaves.algebraicDeRhamSheafComplex X)
  let a := OpenForms.deRhamSheafDirectImageInt f
  let b := ((Sheaves.directImage f).mapHomologicalComplex (.up ℤ)).map (Analytic.De.algebraicSheafIntExtensionIso X).hom
  let c := (Analytic.De.algebraicSheafIntExtensionIso Y).hom
  let d := HomologicalComplex.extendMap (Sheaf.CochainPullback.deRhamSheafDirectImage f) (ComplexShape.embeddingUpIntGE 0)
  have h : a ≫ b ≫ e.hom = c ≫ d := ExtensionNaturality.algebraicSheafIntExtensionIso_naturality f
  change c ≫ (d ≫ e.inv) = a ≫ b
  exact (Category.assoc c d e.inv).symm.trans
    (e.comp_inv_eq.mpr (h.symm.trans (Category.assoc a b e.hom).symm))

theorem algebraicInverseImage_extension_square :
    ((Sheaves.inverseImage f).mapHomologicalComplex (.up ℤ)).map (Analytic.De.algebraicSheafIntExtensionIso Y).hom ≫
      (Complex.Extension.mapExtendIso (Sheaves.inverseImage f) (ComplexShape.embeddingUpIntGE 0)
        (Sheaves.algebraicDeRhamSheafComplex Y)).hom ≫
      HomologicalComplex.extendMap (Sheaf.CochainPullback.deRhamSheafPullback f) (ComplexShape.embeddingUpIntGE 0) =
    OpenForms.deRhamSheafPullbackInt f ≫ (Analytic.De.algebraicSheafIntExtensionIso X).hom := by
  have h := ImageAdjointNaturality.directImageAdjointComplexMap_square f.left.base (OpenForms.deRhamSheafDirectImageInt f)
    (ImageExtensionSquare.extendDirectImageComplexMap f.left.base (Sheaf.CochainPullback.deRhamSheafDirectImage f))
    (Analytic.De.algebraicSheafIntExtensionIso Y).hom (Analytic.De.algebraicSheafIntExtensionIso X).hom
    (algebraicDirectImage_extension_square f)
  erw [AdjointIntegerExtension.directImageAdjointComplexMap_extend] at h
  exact h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.InverseExtension
