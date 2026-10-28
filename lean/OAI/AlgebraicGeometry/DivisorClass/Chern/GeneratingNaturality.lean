import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FrameNaturality
import OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingPointTransitions

/-! # Generating Naturality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingNaturality

noncomputable section

/-! Original Chern-class naturality for the algebraic bundle constructed from a projective morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem generatingAlgebraicLineBundle_firstChern_naturality
    {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} {n : ℕ}
    (f : Y.toOver ⟶ X.toOver) (g : X.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver) :
    First.firstChernClassQ Y (GeneratingLineBundle.generatingAlgebraicLineBundle Y (f ≫ g)) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) 2
        (First.firstChernClassQ X (GeneratingLineBundle.generatingAlgebraicLineBundle X g)) := by
  refine Regular.FrameNaturality.firstChernClassQ_naturality_of_regularFrames
    (GeneratingFrames.generatingAlgebraicSectionFrameAtlas X g) (GeneratingFrames.generatingAlgebraicSectionFrameAtlas Y (f ≫ g)) f ?_ ?_
  · intro i p hi
    change (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (f ≫ g) p).left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp]
    exact hi
  · intro i j p hi hj
    rw [GeneratingPointTransitions.generatingAlgebraicFrame_pointTransition, GeneratingPointTransitions.generatingAlgebraicFrame_pointTransition,
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingNaturality
