import OAI.RepresentationTheory.Theta.Geometric.QuotientIndexedFrames
import OAI.RepresentationTheory.Theta.Geometric.ModuleIsoFrameUnits

/-! # Iso Frame Units -/

namespace OAI.RepresentationTheory.Theta.Geometric.IsoFrameUnits

noncomputable section

section

/-! Regular coefficients of an isomorphism between two actual theta
quotient bundles, with exact restriction compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {n m : ℕ}
    (fS fT : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (gS gT : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m)
    (e : (AlgebraicQuotient.algebraicThetaQuotient fS gS).sheaf ≅ (AlgebraicQuotient.algebraicThetaQuotient fT gT).sheaf)

def thetaIsoFrameOpen (i : QuotientIndexedFrames.ThetaFrameIndex n m × QuotientIndexedFrames.ThetaFrameIndex n m) : X.Opens :=
  ProductFrames.thetaQuotientOpen fS gS i.1.1 i.1.2 ⊓ ProductFrames.thetaQuotientOpen fT gT i.2.1 i.2.2

def thetaIsoFrameUnitOn (i : QuotientIndexedFrames.ThetaFrameIndex n m × QuotientIndexedFrames.ThetaFrameIndex n m)
    (W : X.Opens) (h : W ≤ thetaIsoFrameOpen fS fT gS gT i) : Γ(X, W)ˣ :=
  ModuleIsoFrameUnits.moduleIsoFrameUnit e W
    (QuotientIndexedFrames.thetaQuotientIndexedFrame fS gS i.1 W (h.trans inf_le_left))
    (QuotientIndexedFrames.thetaQuotientIndexedFrame fT gT i.2 W (h.trans inf_le_right))

theorem thetaIsoFrameUnitOn_restrict (i : QuotientIndexedFrames.ThetaFrameIndex n m × QuotientIndexedFrames.ThetaFrameIndex n m)
    {U W : X.Opens} (h : W ≤ U) (hU : U ≤ thetaIsoFrameOpen fS fT gS gT i) :
    PowerGaugeCover.restrictRegularUnit h (thetaIsoFrameUnitOn fS fT gS gT e i U hU) =
      thetaIsoFrameUnitOn fS fT gS gT e i W (h.trans hU) := by
  unfold thetaIsoFrameUnitOn
  rw [ModuleIsoFrameUnits.moduleIsoFrameUnit_restrict, QuotientIndexedFrames.thetaQuotientIndexedFrame_restrict,
    QuotientIndexedFrames.thetaQuotientIndexedFrame_restrict]

end

/-! Evaluated coefficients of a native theta-quotient isomorphism satisfy
the exact analytic change-of-frame equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (fS fT : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (gS gT : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))

theorem thetaIsoFrameUnitOn_transition_value
    (e : (AlgebraicQuotient.algebraicThetaQuotient fS.left gS.left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient fT.left gT.left).sheaf)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (s t : Φ.space)
    (hfS : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fS p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk s)))
    (hgS : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map gS p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk s)))
    (hfT : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fT p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk t)))
    (hgT : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map gT p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk t)))
    (i j : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension ×
      QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension)
    (W : X.left.Opens)
    (hi : W ≤ thetaIsoFrameOpen fS.left fT.left gS.left gT.left i)
    (hj : W ≤ thetaIsoFrameOpen fS.left fT.left gS.left gT.left j)
    (hp : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W) :
    Complex.SectionEvaluation.complexSectionValue p.left W hp
        (thetaIsoFrameUnitOn fS.left fT.left gS.left gT.left e i W hi : Γ(X.left, W)) *
      (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G j.1.1 j.1.2 s / ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1.1 i.1.2 s) =
    (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G j.2.1 j.2.2 t / ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.2.1 i.2.2 t) *
      Complex.SectionEvaluation.complexSectionValue p.left W hp
        (thetaIsoFrameUnitOn fS.left fT.left gS.left gT.left e j W hj : Γ(X.left, W)) := by
  have H := congrArg (fun u : Γ(X.left, W)ˣ => Complex.SectionEvaluation.complexSectionValue p.left W hp (u : Γ(X.left, W)))
    (ModuleIsoFrameUnits.moduleIsoFrameUnit_transition e W
      (QuotientIndexedFrames.thetaQuotientIndexedFrame fS.left gS.left i.1 W (hi.trans inf_le_left))
      (QuotientIndexedFrames.thetaQuotientIndexedFrame fS.left gS.left j.1 W (hj.trans inf_le_left))
      (QuotientIndexedFrames.thetaQuotientIndexedFrame fT.left gT.left i.2 W (hi.trans inf_le_right))
      (QuotientIndexedFrames.thetaQuotientIndexedFrame fT.left gT.left j.2 W (hj.trans inf_le_right)))
  simp only [Units.val_mul, map_mul] at H
  rw [QuotientIndexedFrames.thetaQuotientIndexedFrame_transition_value F G fS gS p s hfS hgS,
    QuotientIndexedFrames.thetaQuotientIndexedFrame_transition_value F G fT gT p t hfT hgT] at H
  exact H

theorem gauge_coefficient_independent (r r' s s' t t' : ℂ)
    (hs : s ≠ 0) (hs' : s' ≠ 0) (ht : t ≠ 0)
    (h : r * (s' / s) = (t' / t) * r') : r * t / s = r' * t' / s' := by
  field_simp [hs, hs', ht] at h ⊢
  linear_combination h

end

end OAI.RepresentationTheory.Theta.Geometric.IsoFrameUnits
