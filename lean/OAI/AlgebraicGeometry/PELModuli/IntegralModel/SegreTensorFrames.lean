import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.PresentationFrames
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames

/-! # Segre Tensor Frames -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SegreTensorFrames

noncomputable section

/-! Actual frames of the O(1,1) sheaf on a product, with transitions equal
to products of the coordinate ratios in the corrected Presentations Segre predicate. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

namespace PolarizationEmbedding

attribute [local instance] MvPolynomial.gradedAlgebra
variable {S : Scheme} {X Y : Over S}
  (BX : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) (BY : HilbertScheme.Presentations.Has.Core.ProjectivePresentation Y)

def segreChartOpen (q : Fin (BX.dimension + 1) × Fin (BY.dimension + 1)) : (X ⨯ Y).left.Opens :=
  (prod.fst : X ⨯ Y ⟶ X).left ⁻¹ᵁ BX.coordinateOpen q.1 ⊓
    (prod.snd : X ⨯ Y ⟶ Y).left ⁻¹ᵁ BY.coordinateOpen q.2

theorem segreChartOpens_cover : iSup (segreChartOpen BX BY) = ⊤ := by
  have hL := (prod.fst : X ⨯ Y ⟶ X).left.iSup_preimage_eq_top (Presentations.PresentationFrames.PolarizationEmbedding.e34_coordinateOpens_cover BX)
  have hR := (prod.snd : X ⨯ Y ⟶ Y).left.iSup_preimage_eq_top (Presentations.PresentationFrames.PolarizationEmbedding.e34_coordinateOpens_cover BY)
  simp only [segreChartOpen, iSup_prod, ← inf_iSup_eq, hR, inf_top_eq]
  exact hL

def segreLeftHyperplane (j : Fin (BX.dimension + 1)) : (X ⨯ Y).left.Modules :=
  (Scheme.Modules.pullback ((prod.fst : X ⨯ Y ⟶ X).left ≫ BX.coefficientEmbedding)).obj
    (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := Γ(S, ⊤)) j)

def segreRightHyperplane (j : Fin (BY.dimension + 1)) : (X ⨯ Y).left.Modules :=
  (Scheme.Modules.pullback ((prod.snd : X ⨯ Y ⟶ Y).left ≫ BY.coefficientEmbedding)).obj
    (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := Γ(S, ⊤)) j)

def segreLeftFrame (j : Fin (BX.dimension + 1))
    (q : Fin (BX.dimension + 1) × Fin (BY.dimension + 1)) :
    (segreLeftHyperplane (Y := Y) BX j).restrict (segreChartOpen BX BY q).ι ≅
      SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (segreChartOpen BX BY q).toScheme :=
  SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization inf_le_left
    (HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame ((prod.fst : X ⨯ Y ⟶ X).left ≫ BX.coefficientEmbedding) j q.1)

def segreRightFrame (j : Fin (BY.dimension + 1))
    (q : Fin (BX.dimension + 1) × Fin (BY.dimension + 1)) :
    (segreRightHyperplane (X := X) BY j).restrict (segreChartOpen BX BY q).ι ≅
      SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (segreChartOpen BX BY q).toScheme :=
  SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization inf_le_right
    (HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame ((prod.snd : X ⨯ Y ⟶ Y).left ≫ BY.coefficientEmbedding) j q.2)

theorem segreLeftFrame_transition_on (j : Fin (BX.dimension + 1))
    (q r : Fin (BX.dimension + 1) × Fin (BY.dimension + 1))
    (U : (X ⨯ Y).left.Opens) (hq : U ≤ segreChartOpen BX BY q) (hr : U ≤ segreChartOpen BX BY r) :
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hq (segreLeftFrame BX BY j q)).hom =
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hr (segreLeftFrame BX BY j r)).hom ≫
        SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (U.topIso.inv
          ((prod.fst : X ⨯ Y ⟶ X).left.appLE (BX.coordinateOpen q.1) U
            (hq.trans inf_le_left) (BX.coordinateRatio q.1 r.1))) := by
  simp only [segreLeftFrame, SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp]
  have h := Projective.FrameRatios.PolarizationEmbedding.hyperplanePullbackFrame_transition_on
    ((prod.fst : X ⨯ Y ⟶ X).left ≫ BX.coefficientEmbedding) j q.1 r.1 U
      (hq.trans inf_le_left) (hr.trans inf_le_left)
  rw [Presentations.PresentationFrames.PolarizationEmbedding.e34_compositeCoordinateRatio] at h
  exact h

theorem segreRightFrame_transition_on (j : Fin (BY.dimension + 1))
    (q r : Fin (BX.dimension + 1) × Fin (BY.dimension + 1))
    (U : (X ⨯ Y).left.Opens) (hq : U ≤ segreChartOpen BX BY q) (hr : U ≤ segreChartOpen BX BY r) :
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hq (segreRightFrame BX BY j q)).hom =
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hr (segreRightFrame BX BY j r)).hom ≫
        SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (U.topIso.inv
          ((prod.snd : X ⨯ Y ⟶ Y).left.appLE (BY.coordinateOpen q.2) U
            (hq.trans inf_le_right) (BY.coordinateRatio q.2 r.2))) := by
  simp only [segreRightFrame, SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp]
  have h := Projective.FrameRatios.PolarizationEmbedding.hyperplanePullbackFrame_transition_on
    ((prod.snd : X ⨯ Y ⟶ Y).left ≫ BY.coefficientEmbedding) j q.2 r.2 U
      (hq.trans inf_le_right) (hr.trans inf_le_right)
  rw [Presentations.PresentationFrames.PolarizationEmbedding.e34_compositeCoordinateRatio] at h
  exact h

def segreTensorHyperplane (j : Fin (BX.dimension + 1)) (k : Fin (BY.dimension + 1)) :
    (X ⨯ Y).left.Modules :=
  AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (segreLeftHyperplane (Y := Y) BX j) (segreRightHyperplane (X := X) BY k)

def segreTensorFrame (j : Fin (BX.dimension + 1)) (k : Fin (BY.dimension + 1))
    (q : Fin (BX.dimension + 1) × Fin (BY.dimension + 1)) :
    (segreTensorHyperplane BX BY j k).restrict (segreChartOpen BX BY q).ι ≅
      SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (segreChartOpen BX BY q).toScheme :=
  RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames.algebraicTensorOpenFrame _ _ _ (segreLeftFrame BX BY j q) (segreRightFrame BX BY k q)

theorem segreTensorFrame_transition_on (j : Fin (BX.dimension + 1)) (k : Fin (BY.dimension + 1))
    (q r : Fin (BX.dimension + 1) × Fin (BY.dimension + 1))
    (U : (X ⨯ Y).left.Opens) (hq : U ≤ segreChartOpen BX BY q) (hr : U ≤ segreChartOpen BX BY r) :
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hq (segreTensorFrame BX BY j k q)).hom =
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hr (segreTensorFrame BX BY j k r)).hom ≫
        SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (U.topIso.inv
          (((prod.fst : X ⨯ Y ⟶ X).left.appLE (BX.coordinateOpen q.1) U
            (hq.trans inf_le_left) (BX.coordinateRatio q.1 r.1)) *
          ((prod.snd : X ⨯ Y ⟶ Y).left.appLE (BY.coordinateOpen q.2) U
            (hq.trans inf_le_right) (BY.coordinateRatio q.2 r.2)))) := by
  simp only [segreTensorFrame, RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames.algebraicTensorOpenFrame_restrict, map_mul]
  exact RepresentationTheory.Theta.Geometric.AlgebraicTensorFrames.algebraicTensorOpenFrame_scalar _ _ U _ _ _ _ _ _
    (segreLeftFrame_transition_on BX BY j q r U hq hr)
    (segreRightFrame_transition_on BX BY k q r U hq hr)

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SegreTensorFrames
