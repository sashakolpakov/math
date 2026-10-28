import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.FrameRatios
import OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech

/-! # Presentation Frames -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.PresentationFrames

noncomputable section

/-! Native hyperplane frames and their coordinate-ratio laws for the exact
projective presentations in the corrected Presentations statement. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

namespace PolarizationEmbedding

attribute [local instance] MvPolynomial.gradedAlgebra
variable {S : Scheme} {X : Over S} (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X)

def e34HyperplanePullback (j : Fin (B.dimension + 1)) : X.left.Modules :=
  (Scheme.Modules.pullback B.coefficientEmbedding).obj
    (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := Γ(S, ⊤)) j)

def e34HyperplaneFrame (j i : Fin (B.dimension + 1)) :
    (e34HyperplanePullback B j).restrict (B.coordinateOpen i).ι ≅
      SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (B.coordinateOpen i).toScheme :=
  HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame B.coefficientEmbedding j i

theorem e34HyperplaneFrame_transition_on (j i k : Fin (B.dimension + 1))
    (U : X.left.Opens) (hi : U ≤ B.coordinateOpen i) (hk : U ≤ B.coordinateOpen k) :
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hi (e34HyperplaneFrame B j i)).hom =
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hk (e34HyperplaneFrame B j k)).hom ≫
        SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
          (U.topIso.inv (X.left.presheaf.map (homOfLE hi).op (B.coordinateRatio i k))) := by
  have h := Projective.FrameRatios.PolarizationEmbedding.hyperplanePullbackFrame_transition_on B.coefficientEmbedding j i k U hi hk
  have hr : B.coefficientEmbedding.appLE (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := Γ(S, ⊤)) i) U hi
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := Γ(S, ⊤)) i k) =
    X.left.presheaf.map (homOfLE hi).op (B.coordinateRatio i k) := by
    unfold HilbertScheme.Presentations.Has.Core.ProjectivePresentation.coordinateRatio
    rw [Projective.FrameRatios.PolarizationEmbedding.e34_coordinateRatio_section]
    rfl
  rw [hr] at h
  exact h

theorem e34_coordinateOpens_cover : iSup B.coordinateOpen = ⊤ := by
  have h := B.coefficientEmbedding.iSup_preimage_eq_top
    (SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := Γ(S, ⊤)) (σ := Fin (B.dimension + 1)))
  apply top_unique
  rw [← h]
  apply iSup_le
  intro i
  exact le_iSup B.coordinateOpen i.down

theorem e34_compositeCoordinateRatio {Y : Scheme} (f : Y ⟶ X.left)
    (i k : Fin (B.dimension + 1)) (U : Y.Opens) (hU : U ≤ f ⁻¹ᵁ B.coordinateOpen i) :
    (f ≫ B.coefficientEmbedding).appLE (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := Γ(S, ⊤)) i) U hU
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := Γ(S, ⊤)) i k) =
        f.appLE (B.coordinateOpen i) U hU (B.coordinateRatio i k) := by
  rw [Scheme.Hom.comp_appLE]
  change f.appLE (B.coordinateOpen i) U hU
    (B.coefficientEmbedding.app (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := Γ(S, ⊤)) i)
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := Γ(S, ⊤)) i k)) = _
  apply congrArg (f.appLE (B.coordinateOpen i) U hU)
  exact congrArg (B.coefficientEmbedding.app (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := Γ(S, ⊤)) i))
    (Projective.FrameRatios.PolarizationEmbedding.e34_coordinateRatio_section (R := ↑Γ(S, ⊤)) i k).symm

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.PresentationFrames
