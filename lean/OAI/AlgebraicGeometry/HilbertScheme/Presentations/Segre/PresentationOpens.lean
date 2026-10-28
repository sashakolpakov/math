import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.CoefficientLift
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.OpenRatioSections
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ReindexOpens

/-! # Presentation Opens -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.PresentationOpens.Core

noncomputable section

/-! The constructed Presentations Segre presentation has exactly the product
coordinate opens required by the statement's O(1,1) condition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {S : Scheme.{u}} {X Y : Over S}
variable (BX : Has.Core.ProjectivePresentation X) (BY : Has.Core.ProjectivePresentation Y)

def segrePresentationCoordinateEquiv : Fin ((Relative.SegrePresentation.Core.segreProductPresentation BX BY).dimension + 1) ≃
    Fin (BX.dimension + 1) × Fin (BY.dimension + 1) :=
  (AbelianModuli.HilbertConstruction.Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} BX.dimension BY.dimension)).symm.trans
    (Equiv.prodCongr Equiv.ulift Equiv.ulift)

theorem segreCoefficientLift_preimage_coordinateOpen
    (i : Fin (BX.dimension + 1)) (j : Fin (BY.dimension + 1)) :
    (prod.fst : X ⨯ Y ⟶ X).left ⁻¹ᵁ BX.coordinateOpen i ⊓
      (prod.snd : X ⨯ Y ⟶ Y).left ⁻¹ᵁ BY.coordinateOpen j =
        CoefficientLift.Core.segreCoefficientLift BX BY ⁻¹ᵁ OpenRatioSections.segreCoordinateOpen Γ(S, ⊤) (ULift.up i, ULift.up j) := by
  let k := CoefficientLift.Core.segreCoefficientLift BX BY
  have hr := congrArg (fun f : (X ⨯ Y).left ⟶ Proj (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) BX.dimension) =>
      f ⁻¹ᵁ Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) BX.dimension) (MvPolynomial.X i))
    (CoefficientLift.Core.segreCoefficientLift_row BX BY)
  have hc := congrArg (fun f : (X ⨯ Y).left ⟶ Proj (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) BY.dimension) =>
      f ⁻¹ᵁ Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) BY.dimension) (MvPolynomial.X j))
    (CoefficientLift.Core.segreCoefficientLift_column BX BY)
  exact (congrArg₂ (fun U V => U ⊓ V) hr.symm hc.symm).trans
    (congrArg (fun U => k ⁻¹ᵁ U) (AbelianModuli.HilbertConstruction.Segre.ProjectionPreimages.segreProjections_preimage Γ(S, ⊤) (ULift.up i, ULift.up j)))

theorem segreProductPresentation_coordinateOpen
    (i : Fin (BX.dimension + 1)) (j : Fin (BY.dimension + 1)) :
    (Relative.SegrePresentation.Core.segreProductPresentation BX BY).coordinateOpen ((segrePresentationCoordinateEquiv BX BY).symm (i, j)) =
      CoefficientLift.Core.segreCoefficientLift BX BY ⁻¹ᵁ OpenRatioSections.segreCoordinateOpen Γ(S, ⊤) (ULift.up i, ULift.up j) := by
  let p : AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} BX.dimension BY.dimension := (ULift.up i, ULift.up j)
  let e := AbelianModuli.HilbertConstruction.Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} BX.dimension BY.dimension)
  let k := CoefficientLift.Core.segreCoefficientLift BX BY
  let U := Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤)
    (AbelianModuli.HilbertConstruction.Affine.SegreOver.segreProjectiveDimension.{u} BX.dimension BY.dimension)) (MvPolynomial.X (e p))
  have hc := congrArg (fun f : (X ⨯ Y).left ⟶ Proj (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤)
      (AbelianModuli.HilbertConstruction.Affine.SegreOver.segreProjectiveDimension.{u} BX.dimension BY.dimension)) => f ⁻¹ᵁ U)
    (CoefficientLift.Core.segreCoefficientLift_embedding BX BY)
  have hr : (AbelianModuli.HilbertConstruction.Projective.SpaceReindex.affineProjectiveSpaceReindexIso Γ(S, ⊤) e).hom.left ⁻¹ᵁ U =
      Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} BX.dimension BY.dimension) Γ(S, ⊤)) (MvPolynomial.X p) :=
    (Projective.ReindexOpens.e33ProjectiveReindex_preimage_basicOpen Γ(S, ⊤) e (e p)).trans
      (congrArg (fun q => Proj.basicOpen
        (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} BX.dimension BY.dimension) Γ(S, ⊤)) (MvPolynomial.X q))
          (e.symm_apply_apply p))
  have hi : (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreProjectiveInclusion Γ(S, ⊤)) ⁻¹ᵁ
      Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} BX.dimension BY.dimension) Γ(S, ⊤)) (MvPolynomial.X p) =
        OpenRatioSections.segreCoordinateOpen Γ(S, ⊤) p :=
    Proj.map_preimage_basicOpen (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (AbelianModuli.HilbertConstruction.Segre.HomogeneousRelations.segreHomogeneousIdeal Γ(S, ⊤)))
      (Homogeneous.Quotient.HomogeneousQuotient.irrelevant_quotient_le_map _) (MvPolynomial.X p)
  exact hc.trans ((congrArg (fun V => k ⁻¹ᵁ (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreProjectiveInclusion Γ(S, ⊤) ⁻¹ᵁ V)) hr).trans
    (congrArg (fun V => k ⁻¹ᵁ V) hi))

theorem segreProductPresentation_productCoordinateOpen
    (i : Fin (BX.dimension + 1)) (j : Fin (BY.dimension + 1)) :
    (prod.fst : X ⨯ Y ⟶ X).left ⁻¹ᵁ BX.coordinateOpen i ⊓
      (prod.snd : X ⨯ Y ⟶ Y).left ⁻¹ᵁ BY.coordinateOpen j =
        (Relative.SegrePresentation.Core.segreProductPresentation BX BY).coordinateOpen
          ((segrePresentationCoordinateEquiv BX BY).symm (i, j)) :=
  (segreCoefficientLift_preimage_coordinateOpen BX BY i j).trans
    (segreProductPresentation_coordinateOpen BX BY i j).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.PresentationOpens.Core
