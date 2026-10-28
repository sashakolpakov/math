import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.PresentationOpens
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionPullbackComposition

/-! # Presentation Row Column -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.PresentationRowColumn.Core

noncomputable section

/-! Pulling the row and column sections through the Segre coefficient
map recovers the original projective presentation's coordinate ratios. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X Y : Over S}
variable (BX : Has.Core.ProjectivePresentation X) (BY : Has.Core.ProjectivePresentation Y)

abbrev segreProductCoordinateOpen (i : Fin (BX.dimension + 1)) (j : Fin (BY.dimension + 1)) :
    (X ⨯ Y).left.Opens :=
  (prod.fst : X ⨯ Y ⟶ X).left ⁻¹ᵁ BX.coordinateOpen i ⊓
    (prod.snd : X ⨯ Y ⟶ Y).left ⁻¹ᵁ BY.coordinateOpen j

theorem segrePresentation_rowRatio
    (i a : Fin (BX.dimension + 1)) (j : Fin (BY.dimension + 1)) :
    (CoefficientLift.Core.segreCoefficientLift BX BY).appLE (OpenRatioSections.segreCoordinateOpen Γ(S, ⊤) (ULift.up i, ULift.up j))
      (segreProductCoordinateOpen BX BY i j) (PresentationOpens.Core.segreCoefficientLift_preimage_coordinateOpen BX BY i j).le
      (OpenRatioSections.segreRowRatioSection Γ(S, ⊤) (ULift.up i, ULift.up j) a) =
        (prod.fst : X ⨯ Y ⟶ X).left.appLE (BX.coordinateOpen i)
          (segreProductCoordinateOpen BX BY i j) inf_le_left (BX.coordinateRatio i a) := by
  let k := CoefficientLift.Core.segreCoefficientLift BX BY
  let r := AbelianModuli.HilbertConstruction.Segre.ProjectionGluing.segreRowProjection Γ(S, ⊤) BX.dimension BY.dimension
  let p := (prod.fst : X ⨯ Y ⟶ X).left
  let f := BX.coefficientEmbedding
  let U := Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) BX.dimension) (MvPolynomial.X i)
  let V := OpenRatioSections.segreCoordinateOpen Γ(S, ⊤) (ULift.up i, ULift.up j)
  let W := segreProductCoordinateOpen BX BY i j
  let s := Proj.awayToSection (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) BX.dimension) (MvPolynomial.X i)
    (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (MvPolynomial.X a))
  have hk : W ≤ k ⁻¹ᵁ V := (PresentationOpens.Core.segreCoefficientLift_preimage_coordinateOpen BX BY i j).le
  have hr : V ≤ r ⁻¹ᵁ U := OpenRatioSections.segreCoordinateOpen_le_row Γ(S, ⊤) (ULift.up i, ULift.up j)
  have hkr : W ≤ (k ≫ r) ⁻¹ᵁ U := hk.trans (k.preimage_mono hr)
  have hpf : W ≤ (p ≫ f) ⁻¹ᵁ U := inf_le_left
  exact (SectionPullbackComposition.appLE_comp_apply k r U V W hr hk hkr s).trans
    ((SectionPullbackComposition.appLE_congr_apply (CoefficientLift.Core.segreCoefficientLift_row BX BY) U W hkr hpf s).trans
      (SectionPullbackComposition.appLE_comp_preimage_apply p f U W hpf s))

theorem segrePresentation_columnRatio
    (i : Fin (BX.dimension + 1)) (j b : Fin (BY.dimension + 1)) :
    (CoefficientLift.Core.segreCoefficientLift BX BY).appLE (OpenRatioSections.segreCoordinateOpen Γ(S, ⊤) (ULift.up i, ULift.up j))
      (segreProductCoordinateOpen BX BY i j) (PresentationOpens.Core.segreCoefficientLift_preimage_coordinateOpen BX BY i j).le
      (OpenRatioSections.segreColumnRatioSection Γ(S, ⊤) (ULift.up i, ULift.up j) b) =
        (prod.snd : X ⨯ Y ⟶ Y).left.appLE (BY.coordinateOpen j)
          (segreProductCoordinateOpen BX BY i j) inf_le_right (BY.coordinateRatio j b) := by
  let k := CoefficientLift.Core.segreCoefficientLift BX BY
  let r := AbelianModuli.HilbertConstruction.Segre.ProjectionGluing.segreColumnProjection Γ(S, ⊤) BX.dimension BY.dimension
  let p := (prod.snd : X ⨯ Y ⟶ Y).left
  let f := BY.coefficientEmbedding
  let U := Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) BY.dimension) (MvPolynomial.X j)
  let V := OpenRatioSections.segreCoordinateOpen Γ(S, ⊤) (ULift.up i, ULift.up j)
  let W := segreProductCoordinateOpen BX BY i j
  let s := Proj.awayToSection (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) BY.dimension) (MvPolynomial.X j)
    (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize j (MvPolynomial.X b))
  have hk : W ≤ k ⁻¹ᵁ V := (PresentationOpens.Core.segreCoefficientLift_preimage_coordinateOpen BX BY i j).le
  have hr : V ≤ r ⁻¹ᵁ U := OpenRatioSections.segreCoordinateOpen_le_column Γ(S, ⊤) (ULift.up i, ULift.up j)
  have hkr : W ≤ (k ≫ r) ⁻¹ᵁ U := hk.trans (k.preimage_mono hr)
  have hpf : W ≤ (p ≫ f) ⁻¹ᵁ U := inf_le_right
  exact (SectionPullbackComposition.appLE_comp_apply k r U V W hr hk hkr s).trans
    ((SectionPullbackComposition.appLE_congr_apply (CoefficientLift.Core.segreCoefficientLift_column BX BY) U W hkr hpf s).trans
      (SectionPullbackComposition.appLE_comp_preimage_apply p f U W hpf s))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.PresentationRowColumn.Core
