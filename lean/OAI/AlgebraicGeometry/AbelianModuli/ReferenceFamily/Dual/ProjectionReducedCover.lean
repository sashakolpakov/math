import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation

/-! # Projection Reduced Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProjectionReducedCover

noncomputable section

/-! The reduced cover of the original dual-product projection is
the original cover itself. This keeps translation-frame coefficients
on the same actual opens as the line logarithmic cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

theorem dualProjectionReducedOpen (U : X.left.Opens) :
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ ((snd (LieRanks.dualNumberTest ℂ) X).left ⁻¹ᵁ U) = U := by
  have h := congrArg Over.Hom.left (ReductionOpens.dualBaseChangeReduction_projection X)
  change ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ≫ (snd (LieRanks.dualNumberTest ℂ) X).left) ⁻¹ᵁ U = U
  exact congrArg (fun f : X.left ⟶ X.left => f ⁻¹ᵁ U) h

theorem dualProjectionReducedCover {I : Type} (U : I → X.left.Opens) :
    CechCoefficient.dualReducedCechCover X (fun i => (snd (LieRanks.dualNumberTest ℂ) X).left ⁻¹ᵁ U i) = U := by
  funext i
  exact dualProjectionReducedOpen X (U i)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ProjectionReducedCover
