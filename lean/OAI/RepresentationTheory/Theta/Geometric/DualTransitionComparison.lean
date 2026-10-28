import OAI.RepresentationTheory.Theta.Geometric.Dual.UnitEvaluation
import OAI.RepresentationTheory.Theta.Geometric.QuotientIndexedFrames

/-! # Dual Transition Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric.DualTransitionComparison

noncomputable section

section

/-! Exact evaluation of native theta-frame transitions at arbitrary
dual-number points. The value depends only on the two actual projective
composites of that point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
theorem thetaQuotientFrame_transition_dualValue {X : Scheme} {n m : ℕ}
    (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m)
    (p : Spec (.of (DualNumber ℂ)) ⟶ X) (i j : QuotientIndexedFrames.ThetaFrameIndex n m) (W : X.Opens)
    (hi : W ≤ ProductFrames.thetaQuotientOpen f g i.1 i.2) (hj : W ≤ ProductFrames.thetaQuotientOpen f g j.1 j.2)
    (hp : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤ p ⁻¹ᵁ W)
    (hF : W ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i.1 j.1)
    (hG : W ≤ g ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i.2 j.2) :
    Dual.OpenSectionValues.dualSectionValue p W hp
      (IntrinsicFrame.TransitionUnits.frameTransitionUnit (AlgebraicQuotient.algebraicThetaQuotient f g).sheaf W
        (QuotientIndexedFrames.thetaQuotientIndexedFrame f g i W hi) (QuotientIndexedFrames.thetaQuotientIndexedFrame f g j W hj) : Γ(X, W)) =
    Dual.OpenSectionValues.dualSectionValue (p ≫ g) (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i.2 j.2)
        (hp.trans (p.preimage_mono hG))
        (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := ℂ) i.2 j.2 : Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m, _)) *
      (Dual.OpenSectionValues.dualSectionValue (p ≫ f) (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i.1 j.1)
        (hp.trans (p.preimage_mono hF))
        (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := ℂ) i.1 j.1 : Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n, _)))⁻¹ := by
  have ht := FrameTransitionUnitCoherence.frameTransitionUnit_unique (AlgebraicQuotient.algebraicThetaQuotient f g).sheaf W _ _ _
    (ProductFrames.thetaQuotientFrameOn_transition f g i.1 j.1 i.2 j.2 W hF hG)
  change Dual.OpenSectionValues.dualSectionValue p W hp
    (IntrinsicFrame.TransitionUnits.frameTransitionUnit (AlgebraicQuotient.algebraicThetaQuotient f g).sheaf W
      (ProductFrames.thetaQuotientFrameOn f g i.1 i.2 W _ _) (ProductFrames.thetaQuotientFrameOn f g j.1 j.2 W _ _) : Γ(X, W)) = _
  rw [← ht]
  simp only [Units.val_mul, map_mul, Dual.UnitEvaluation.dualRingHom_unit_inv, Dual.UnitEvaluation.restrictRegularUnit_dualValue,
    Dual.UnitEvaluation.projectivePullbackTransitionUnit_dualValue]

end

/-! Native theta-frame transition values agree whenever their actual
dual-number projective points agree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem thetaQuotientOpen_overlap {X : Scheme} {n m : ℕ}
    (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m)
    (i j : QuotientIndexedFrames.ThetaFrameIndex n m) (W : X.Opens)
    (hi : W ≤ ProductFrames.thetaQuotientOpen f g i.1 i.2) (hj : W ≤ ProductFrames.thetaQuotientOpen f g j.1 j.2) :
    W ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i.1 j.1 ∧
      W ≤ g ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i.2 j.2 := by
  constructor
  · rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
    exact le_inf (hi.trans inf_le_left) (hj.trans inf_le_left)
  · rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
    exact le_inf (hi.trans inf_le_right) (hj.trans inf_le_right)

set_option backward.isDefEq.respectTransparency false in
theorem thetaQuotientFrame_transition_dualValue_congr {X Y : Scheme} {n m : ℕ}
    (fX : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (fY : Y ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (gX : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m) (gY : Y ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m)
    (pX : Spec (.of (DualNumber ℂ)) ⟶ X) (pY : Spec (.of (DualNumber ℂ)) ⟶ Y)
    (hf : pX ≫ fX = pY ≫ fY) (hg : pX ≫ gX = pY ≫ gY)
    (i j : QuotientIndexedFrames.ThetaFrameIndex n m) (U : X.Opens) (W : Y.Opens)
    (hiX : U ≤ ProductFrames.thetaQuotientOpen fX gX i.1 i.2) (hjX : U ≤ ProductFrames.thetaQuotientOpen fX gX j.1 j.2)
    (hiY : W ≤ ProductFrames.thetaQuotientOpen fY gY i.1 i.2) (hjY : W ≤ ProductFrames.thetaQuotientOpen fY gY j.1 j.2)
    (hpX : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤ pX ⁻¹ᵁ U)
    (hpY : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤ pY ⁻¹ᵁ W) :
    Dual.OpenSectionValues.dualSectionValue pX U hpX
      (IntrinsicFrame.TransitionUnits.frameTransitionUnit (AlgebraicQuotient.algebraicThetaQuotient fX gX).sheaf U
        (QuotientIndexedFrames.thetaQuotientIndexedFrame fX gX i U hiX) (QuotientIndexedFrames.thetaQuotientIndexedFrame fX gX j U hjX) : Γ(X, U)) =
    Dual.OpenSectionValues.dualSectionValue pY W hpY
      (IntrinsicFrame.TransitionUnits.frameTransitionUnit (AlgebraicQuotient.algebraicThetaQuotient fY gY).sheaf W
        (QuotientIndexedFrames.thetaQuotientIndexedFrame fY gY i W hiY) (QuotientIndexedFrames.thetaQuotientIndexedFrame fY gY j W hjY) : Γ(Y, W)) := by
  obtain ⟨hFX, hGX⟩ := thetaQuotientOpen_overlap fX gX i j U hiX hjX
  obtain ⟨hFY, hGY⟩ := thetaQuotientOpen_overlap fY gY i j W hiY hjY
  rw [thetaQuotientFrame_transition_dualValue fX gX pX i j U hiX hjX hpX hFX hGX,
    thetaQuotientFrame_transition_dualValue fY gY pY i j W hiY hjY hpY hFY hGY]
  exact congrArg₂ (fun a b : DualNumber ℂ => a * b⁻¹)
    (Dual.OpenSectionValues.dualSectionValue_congr _ _ hg _ _ _ _)
    (Dual.OpenSectionValues.dualSectionValue_congr _ _ hf _ _ _ _)

end

end OAI.RepresentationTheory.Theta.Geometric.DualTransitionComparison
