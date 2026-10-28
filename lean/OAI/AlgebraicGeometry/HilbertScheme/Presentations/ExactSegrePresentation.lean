import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.PresentationTargetRatio
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.OpenRatioPullback

/-! # Exact Segre Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ExactSegrePresentation.Core

noncomputable section

/-! The actual closed Segre product embedding satisfies precisely the
O(1,1) chart-domain and regular-section conditions in the Presentations statement,
over every base scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X Y : Over S}

theorem segreProductPresentation_isSegre
    (BX : Has.Core.ProjectivePresentation X) (BY : Has.Core.ProjectivePresentation Y) :
    Segre.Open.Core.IsSegrePresentation BX BY (Relative.SegrePresentation.Core.segreProductPresentation BX BY) := by
  refine ⟨Segre.PresentationOpens.Core.segrePresentationCoordinateEquiv BX BY, ?_⟩
  intro i j
  refine ⟨Segre.PresentationOpens.Core.segreProductPresentation_productCoordinateOpen BX BY i j, ?_⟩
  intro a b
  let k : Γ(AbelianModuli.HilbertConstruction.Segre.ProductComparison.segreEquationScheme Γ(S, ⊤) BX.dimension BY.dimension,
      Segre.OpenRatioSections.segreCoordinateOpen Γ(S, ⊤) (ULift.up i, ULift.up j)) ⟶
      Γ((X ⨯ Y).left, Segre.PresentationRowColumn.Core.segreProductCoordinateOpen BX BY i j) :=
    (Segre.CoefficientLift.Core.segreCoefficientLift BX BY).appLE _ _
      (Segre.PresentationOpens.Core.segreCoefficientLift_preimage_coordinateOpen BX BY i j).le
  have hm := congrArg k (Segre.OpenRatioPullback.segreOpen_ratio_identity Γ(S, ⊤) (ULift.up i, ULift.up j) a b)
  exact (Segre.PresentationTargetRatio.Core.segrePresentation_targetRatio BX BY i a j b).trans
    (hm.trans ((map_mul k.hom _ _).trans
      (congrArg₂ (fun x y => x * y) (Segre.PresentationRowColumn.Core.segrePresentation_rowRatio BX BY i a j)
        (Segre.PresentationRowColumn.Core.segrePresentation_columnRatio BX BY i j b))))

theorem exists_segrePresentation (BX : Has.Core.ProjectivePresentation X) (BY : Has.Core.ProjectivePresentation Y) :
    ∃ B : Has.Core.ProjectivePresentation (X ⨯ Y), Segre.Open.Core.IsSegrePresentation BX BY B :=
  ⟨Relative.SegrePresentation.Core.segreProductPresentation BX BY, segreProductPresentation_isSegre BX BY⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ExactSegrePresentation.Core
