import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.CoefficientMap

/-! # Coefficient Lift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.CoefficientLift.Core

noncomputable section

/-! The Segre coefficient map factors through the actual rank-one
matrix scheme, with the two original projective coefficient projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u
variable {S : Scheme.{u}} {X Y : Over S}
variable (BX : Has.Core.ProjectivePresentation X) (BY : Has.Core.ProjectivePresentation Y)

def segreCoefficientLift : (X ⨯ Y).left ⟶
    AbelianModuli.HilbertConstruction.Segre.ProductComparison.segreEquationScheme Γ(S, ⊤) BX.dimension BY.dimension :=
  CoefficientMap.Core.segrePairCoefficientMap BX BY ≫
    (AbelianModuli.HilbertConstruction.Segre.ProjectiveIsomorphism.segreProductSchemeIso Γ(S, ⊤) BX.dimension BY.dimension).inv

theorem segreCoefficientLift_row :
    segreCoefficientLift BX BY ≫ AbelianModuli.HilbertConstruction.Segre.ProjectionGluing.segreRowProjection Γ(S, ⊤) BX.dimension BY.dimension =
      (prod.fst : X ⨯ Y ⟶ X).left ≫ BX.coefficientEmbedding := by
  let e := AbelianModuli.HilbertConstruction.Segre.ProjectiveIsomorphism.segreProductSchemeIso Γ(S, ⊤) BX.dimension BY.dimension
  have he : e.inv ≫ AbelianModuli.HilbertConstruction.Segre.ProjectionGluing.segreRowProjection Γ(S, ⊤) BX.dimension BY.dimension =
      pullback.fst _ _ :=
    (Iso.inv_comp_eq e).mpr (AbelianModuli.HilbertConstruction.Segre.ProductComparison.segreToProduct_fst Γ(S, ⊤) BX.dimension BY.dimension).symm
  exact (Category.assoc (CoefficientMap.Core.segrePairCoefficientMap BX BY) e.inv _).trans
    ((congrArg (fun h => CoefficientMap.Core.segrePairCoefficientMap BX BY ≫ h) he).trans
      (CoefficientMap.Core.segrePairCoefficientMap_fst BX BY))

theorem segreCoefficientLift_column :
    segreCoefficientLift BX BY ≫ AbelianModuli.HilbertConstruction.Segre.ProjectionGluing.segreColumnProjection Γ(S, ⊤) BX.dimension BY.dimension =
      (prod.snd : X ⨯ Y ⟶ Y).left ≫ BY.coefficientEmbedding := by
  let e := AbelianModuli.HilbertConstruction.Segre.ProjectiveIsomorphism.segreProductSchemeIso Γ(S, ⊤) BX.dimension BY.dimension
  have he : e.inv ≫ AbelianModuli.HilbertConstruction.Segre.ProjectionGluing.segreColumnProjection Γ(S, ⊤) BX.dimension BY.dimension =
      pullback.snd _ _ :=
    (Iso.inv_comp_eq e).mpr (AbelianModuli.HilbertConstruction.Segre.ProductComparison.segreToProduct_snd Γ(S, ⊤) BX.dimension BY.dimension).symm
  exact (Category.assoc (CoefficientMap.Core.segrePairCoefficientMap BX BY) e.inv _).trans
    ((congrArg (fun h => CoefficientMap.Core.segrePairCoefficientMap BX BY ≫ h) he).trans
      (CoefficientMap.Core.segrePairCoefficientMap_snd BX BY))

theorem segreCoefficientLift_embedding :
    (Relative.SegrePresentation.Core.segreProductPresentation BX BY).coefficientEmbedding =
      segreCoefficientLift BX BY ≫ AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreProjectiveInclusion Γ(S, ⊤) ≫
        (AbelianModuli.HilbertConstruction.Projective.SpaceReindex.affineProjectiveSpaceReindexIso Γ(S, ⊤)
          (AbelianModuli.HilbertConstruction.Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv
            (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} BX.dimension BY.dimension))).hom.left := by
  rw [CoefficientMap.Core.segreProductPresentation_coefficientEmbedding]
  let d := CoefficientMap.Core.segrePairCoefficientMap BX BY
  let e := AbelianModuli.HilbertConstruction.Segre.ProjectiveIsomorphism.segreProductSchemeIso Γ(S, ⊤) BX.dimension BY.dimension
  let i := AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreProjectiveInclusion (σ := ULift.{u} (Fin (BX.dimension + 1)))
    (τ := ULift.{u} (Fin (BY.dimension + 1))) Γ(S, ⊤)
  let r := (AbelianModuli.HilbertConstruction.Projective.SpaceReindex.affineProjectiveSpaceReindexIso Γ(S, ⊤)
    (AbelianModuli.HilbertConstruction.Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv
      (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} BX.dimension BY.dimension))).hom.left
  change d ≫ ((e.inv ≫ i) ≫ r) = (d ≫ e.inv) ≫ i ≫ r
  simp only [Category.assoc]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.CoefficientLift.Core
