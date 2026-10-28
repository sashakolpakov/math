import OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingFrames
import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FrameAnalyticTransitions
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RatioPointEvaluation

/-! # Generating Point Transitions -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingPointTransitions

noncomputable section

/-! The constructed algebraic bundle's original frame transitions evaluate to the original projective coordinate ratios of the mapped point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

theorem generatingAlgebraicFrame_pointTransition (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {n : ℕ}
    (g : P.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver)
    (i j : Fin (n + 1)) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)
    (hi : p ∈ (GeneratingFrames.generatingAlgebraicSectionFrameAtlas P g).analyticDomain i)
    (hj : p ∈ (GeneratingFrames.generatingAlgebraicSectionFrameAtlas P g).analyticDomain j) :
    (GeneratingFrames.generatingAlgebraicSectionFrameAtlas P g).pointTransition i j p hi hj =
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g p)) := by
  let W := (g.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) ⊓ (g.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n j)
  let q : Line.Bundles.AlgebraicLineBundle.analyticOpen P W := ⟨p, hi, hj⟩
  have hWi : W ≤ g.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i := inf_le_left
  have hWj : W ≤ g.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n j := inf_le_right
  have ht := congrArg (fun r : Γ(P.carrier, W) => Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W r q)
    (GeneratingFrames.generatingAlgebraicFrame_transition_ratio P g i j W hWi hWj)
  have he := Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_appLE g (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) W hWi
    (Projective.RegularRatios.projectiveRegularRatio n i j (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) le_rfl) q
  exact ((GeneratingFrames.generatingAlgebraicSectionFrameAtlas P g).pointTransition_restrict i j W hWi hWj q).trans
    (ht.trans (he.trans (Projective.RatioPointEvaluation.projectiveRegularRatio_point_evaluation n i j
      (Line.Bundles.AlgebraicLineBundle.analyticOpenMap g (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) W hWi q))))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingPointTransitions
