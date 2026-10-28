import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.PresentationRowColumn
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ReindexSections

/-! # Presentation Target Ratio -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.PresentationTargetRatio.Core

noncomputable section

/-! The constructed Segre presentation's finite-index coordinate ratios
are the pullbacks of the actual ambient Segre coordinate sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X Y : Over S}
variable (BX : Has.Core.ProjectivePresentation X) (BY : Has.Core.ProjectivePresentation Y)

theorem segrePresentation_targetRatio
    (i a : Fin (BX.dimension + 1)) (j b : Fin (BY.dimension + 1)) :
    (X ⨯ Y).left.presheaf.map
      (homOfLE (PresentationOpens.Core.segreProductPresentation_productCoordinateOpen BX BY i j).le).op
      ((Relative.SegrePresentation.Core.segreProductPresentation BX BY).coordinateRatio
        ((PresentationOpens.Core.segrePresentationCoordinateEquiv BX BY).symm (i, j))
        ((PresentationOpens.Core.segrePresentationCoordinateEquiv BX BY).symm (a, b))) =
    (CoefficientLift.Core.segreCoefficientLift BX BY).appLE
      (OpenRatioSections.segreCoordinateOpen Γ(S, ⊤) (ULift.up i, ULift.up j))
      (PresentationRowColumn.Core.segreProductCoordinateOpen BX BY i j)
      (PresentationOpens.Core.segreCoefficientLift_preimage_coordinateOpen BX BY i j).le
      (OpenRatioSections.segreAmbientRatioSection Γ(S, ⊤) (ULift.up i, ULift.up j) (ULift.up a, ULift.up b)) := by
  let p : AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} BX.dimension BY.dimension := (ULift.up i, ULift.up j)
  let q : AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} BX.dimension BY.dimension := (ULift.up a, ULift.up b)
  let e := AbelianModuli.HilbertConstruction.Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} BX.dimension BY.dimension)
  let k := CoefficientLift.Core.segreCoefficientLift BX BY
  let t := AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreProjectiveInclusion (σ := ULift.{u} (Fin (BX.dimension + 1)))
    (τ := ULift.{u} (Fin (BY.dimension + 1))) Γ(S, ⊤)
  let r := (AbelianModuli.HilbertConstruction.Projective.SpaceReindex.affineProjectiveSpaceReindexIso Γ(S, ⊤) e).hom.left
  let f := (Relative.SegrePresentation.Core.segreProductPresentation BX BY).coefficientEmbedding
  let U := Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤)
    (AbelianModuli.HilbertConstruction.Affine.SegreOver.segreProjectiveDimension.{u} BX.dimension BY.dimension)) (MvPolynomial.X (e p))
  let V := Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} BX.dimension BY.dimension)
    Γ(S, ⊤)) (MvPolynomial.X p)
  let Z := OpenRatioSections.segreCoordinateOpen Γ(S, ⊤) p
  let W := PresentationRowColumn.Core.segreProductCoordinateOpen BX BY i j
  let s := Projective.ReindexSections.e33CoordinateRatioSection Γ(S, ⊤)
    (AbelianModuli.HilbertConstruction.Affine.SegreOver.segreProjectiveDimension.{u} BX.dimension BY.dimension) (e p) (e q)
  have hr : V ≤ r ⁻¹ᵁ U :=
    ((Projective.ReindexOpens.e33ProjectiveReindex_preimage_basicOpen Γ(S, ⊤) e (e p)).trans
      (congrArg (fun x => Proj.basicOpen
        (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} BX.dimension BY.dimension) Γ(S, ⊤))
        (MvPolynomial.X x)) (e.symm_apply_apply p))).ge
  have ht : Z ≤ t ⁻¹ᵁ V := le_rfl
  have hk : W ≤ k ⁻¹ᵁ Z := (PresentationOpens.Core.segreCoefficientLift_preimage_coordinateOpen BX BY i j).le
  have htr : Z ≤ (t ≫ r) ⁻¹ᵁ U := ht.trans (t.preimage_mono hr)
  have hktr : W ≤ (k ≫ t ≫ r) ⁻¹ᵁ U := hk.trans (k.preimage_mono htr)
  have hf : W ≤ f ⁻¹ᵁ U := (PresentationOpens.Core.segreProductPresentation_productCoordinateOpen BX BY i j).le
  change f.appLE U W hf s = k.appLE Z W hk (OpenRatioSections.segreAmbientRatioSection Γ(S, ⊤) p q)
  have h1 := SectionPullbackComposition.appLE_congr_apply (CoefficientLift.Core.segreCoefficientLift_embedding BX BY) U W hf hktr s
  have h2 := SectionPullbackComposition.appLE_comp_apply k (t ≫ r) U Z W htr hk hktr s
  have h3 := SectionPullbackComposition.appLE_comp_apply t r U V Z hr ht htr s
  have h4 := Projective.ReindexSections.e33ProjectiveReindex_section_apply Γ(S, ⊤) e p q hr
  exact h1.trans (h2.symm.trans
    (congrArg (fun x => k.appLE Z W hk x)
      (h3.symm.trans (congrArg (fun x => t.appLE V Z ht x) h4))))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.PresentationTargetRatio.Core
