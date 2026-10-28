import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FrameAnalyticTransitions

/-! # Generating Frames -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingFrames

noncomputable section

/-! Exact original-convention regular frame transitions of the constructed algebraic bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def generatingAlgebraicSectionFrameAtlas (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {n : ℕ}
    (g : P.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver) :
    Regular.FrameAnalyticTransitions.RegularSectionFrameAtlas (GeneratingLineBundle.generatingAlgebraicLineBundle P g) (Fin (n + 1)) :=
  Regular.FrameAnalyticTransitions.regularCocycleSectionFrameAtlas P (Regular.CocyclePullback.regularCocyclePullback (Projective.RegularLineBundle.projectiveRegularLineCocycle n) g.left)

theorem generatingAlgebraicFrame_transition (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {n : ℕ}
    (g : P.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver)
    (i j : Fin (n + 1)) (W : P.carrier.Opens)
    (hi : W ≤ g.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (hj : W ≤ g.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n j) :
    (generatingAlgebraicSectionFrameAtlas P g).transition i j W hi hj =
      Regular.CocyclePullback.pullbackRegularTransition (Projective.RegularLineBundle.projectiveRegularLineCocycle n) g.left j i W hj hi :=
  Regular.LineFrameTransition.regularLineSectionLinearFrame_transition
    (Regular.CocyclePullback.regularCocyclePullback (Projective.RegularLineBundle.projectiveRegularLineCocycle n) g.left) i j W hi hj

/-- The transition used by the original algebraic Chern class is the pullback
of `Xⱼ / Xᵢ`, with its direction determined by the native section frames. -/
theorem generatingAlgebraicFrame_transition_ratio (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {n : ℕ}
    (g : P.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver)
    (i j : Fin (n + 1)) (W : P.carrier.Opens)
    (hi : W ≤ g.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
    (hj : W ≤ g.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n j) :
    ((generatingAlgebraicSectionFrameAtlas P g).transition i j W hi hj : Γ(P.carrier, W)) =
      Regular.CocyclePullback.regularPullback g.left hi (Projective.RegularRatios.projectiveRegularRatio n i j (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) le_rfl) := by
  rw [generatingAlgebraicFrame_transition]
  change Regular.CocyclePullback.regularPullback g.left
    (show W ≤ g.left ⁻¹ᵁ (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n j ⊓ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) from
      le_inf hj hi)
    (Projective.RegularRatios.projectiveRegularRatio n i j (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n j ⊓ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
      inf_le_right) = _
  have hW : W ≤ g.left ⁻¹ᵁ (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n j ⊓ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) :=
    le_inf hj hi
  exact (congrArg (Regular.CocyclePullback.regularPullback g.left hW)
    (Projective.RegularRatios.projectiveRegularRatio_restrict n i j (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
      (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n j ⊓ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) inf_le_right le_rfl).symm).trans
    (Regular.CocyclePullback.regularPullback_restrict g.left hW inf_le_right
      (Projective.RegularRatios.projectiveRegularRatio n i j (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) le_rfl))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingFrames
