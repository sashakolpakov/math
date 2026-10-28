import OAI.RepresentationTheory.Theta.Geometric.IsoFrameUnits
import OAI.RepresentationTheory.Theta.Geometric.OpenRegularFunctionHolomorphic

/-! # Iso Gauge Compatibility -/

namespace OAI.RepresentationTheory.Theta.Geometric.IsoGaugeCompatibility

noncomputable section

section

/-! Local analytic gauges read directly from regular coefficients of an
actual isomorphism of the two native quotient bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (fS fT : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (gS gT : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))

def localThetaIsoGauge
    (e : (AlgebraicQuotient.algebraicThetaQuotient fS.left gS.left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient fT.left gT.left).sheaf)
    (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension ×
      QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (s t : Φ.space) : ℂ :=
  OpenRegularFunctionValues.openRegularFunctionValue X (IsoFrameUnits.thetaIsoFrameOpen fS.left fT.left gS.left gT.left i)
      (IsoFrameUnits.thetaIsoFrameUnitOn fS.left fT.left gS.left gT.left e i _ le_rfl : Γ(X.left, _)) p *
    ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.2.1 i.2.2 t / ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1.1 i.1.2 s

theorem thetaIsoFrameOpen_mem (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (s t : Φ.space)
    (hfS : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fS p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk s)))
    (hgS : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map gS p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk s)))
    (hfT : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fT p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk t)))
    (hgT : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map gT p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk t)))
    (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension ×
      QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension) :
    p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ IsoFrameUnits.thetaIsoFrameOpen fS.left fT.left gS.left gT.left i ↔
      (F.coordinate i.1.1 s ≠ 0 ∧ G.coordinate i.1.2 s ≠ 0) ∧
      (F.coordinate i.2.1 t ≠ 0 ∧ G.coordinate i.2.2 t ≠ 0) := by
  change ((_ ∈ fS.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen _ i.1.1 ∧
    _ ∈ gS.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen _ i.1.2) ∧
    (_ ∈ fT.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen _ i.2.1 ∧
    _ ∈ gT.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen _ i.2.2)) ↔ _
  rw [ProductValues.thetaCoordinateOpen_mem_of_point F fS p s hfS,
    ProductValues.thetaCoordinateOpen_mem_of_point G gS p s hgS,
    ProductValues.thetaCoordinateOpen_mem_of_point F fT p t hfT,
    ProductValues.thetaCoordinateOpen_mem_of_point G gT p t hgT]

theorem localThetaIsoGauge_ne_zero
    (e : (AlgebraicQuotient.algebraicThetaQuotient fS.left gS.left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient fT.left gT.left).sheaf)
    (i : QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension ×
      QuotientIndexedFrames.ThetaFrameIndex F.projectiveDimension G.projectiveDimension)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (s t : Φ.space)
    (hp : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ IsoFrameUnits.thetaIsoFrameOpen fS.left fT.left gS.left gT.left i)
    (hs : ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1.1 i.1.2 s ≠ 0)
    (ht : ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.2.1 i.2.2 t ≠ 0) :
    localThetaIsoGauge F G fS fT gS gT e i p s t ≠ 0 := by
  unfold localThetaIsoGauge
  rw [OpenRegularFunctionValues.openRegularFunctionValue_of_mem X _ _ p hp]
  apply div_ne_zero (mul_ne_zero _ ht) hs
  exact (Units.isUnit (IsoFrameUnits.thetaIsoFrameUnitOn fS.left fT.left gS.left gT.left e i _ le_rfl)).map
    (Complex.SectionEvaluation.complexSectionValue p.left _ hp) |>.ne_zero

end

/-! The regular local comparison gauges agree on all overlaps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem thetaIsoFrameUnitOn_value {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {n m : ℕ}
    (fS fT : X.left ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (gS gT : X.left ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m)
    (e : (AlgebraicQuotient.algebraicThetaQuotient fS gS).sheaf ≅ (AlgebraicQuotient.algebraicThetaQuotient fT gT).sheaf)
    (i : QuotientIndexedFrames.ThetaFrameIndex n m × QuotientIndexedFrames.ThetaFrameIndex n m) (W : X.left.Opens)
    (hW : W ≤ IsoFrameUnits.thetaIsoFrameOpen fS fT gS gT i)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hp : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W) :
    Complex.SectionEvaluation.complexSectionValue p.left W hp (IsoFrameUnits.thetaIsoFrameUnitOn fS fT gS gT e i W hW : Γ(X.left, W)) =
      OpenRegularFunctionValues.openRegularFunctionValue X (IsoFrameUnits.thetaIsoFrameOpen fS fT gS gT i)
        (IsoFrameUnits.thetaIsoFrameUnitOn fS fT gS gT e i _ le_rfl : Γ(X.left, _)) p := by
  rw [OpenRegularFunctionValues.openRegularFunctionValue_of_mem X _ _ p (hW hp)]
  have H := PowerGaugeCover.restrictRegularUnit_value hW (IsoFrameUnits.thetaIsoFrameUnitOn fS fT gS gT e i _ le_rfl) p.left hp
  rw [IsoFrameUnits.thetaIsoFrameUnitOn_restrict] at H
  exact H

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (fS fT : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (gS gT : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))

theorem localThetaIsoGauge_compatible
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
    (hi : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ IsoFrameUnits.thetaIsoFrameOpen fS.left fT.left gS.left gT.left i)
    (hj : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ IsoFrameUnits.thetaIsoFrameOpen fS.left fT.left gS.left gT.left j) :
    localThetaIsoGauge F G fS fT gS gT e i p s t = localThetaIsoGauge F G fS fT gS gT e j p s t := by
  let W := IsoFrameUnits.thetaIsoFrameOpen fS.left fT.left gS.left gT.left i ⊓
    IsoFrameUnits.thetaIsoFrameOpen fS.left fT.left gS.left gT.left j
  have H := IsoFrameUnits.thetaIsoFrameUnitOn_transition_value F G fS fT gS gT e p s t hfS hgS hfT hgT i j W
    inf_le_left inf_le_right (show p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W from ⟨hi, hj⟩)
  rw [thetaIsoFrameUnitOn_value, thetaIsoFrameUnitOn_value] at H
  have hi' := (thetaIsoFrameOpen_mem F G fS fT gS gT p s t hfS hgS hfT hgT i).mp hi
  have hj' := (thetaIsoFrameOpen_mem F G fS fT gS gT p s t hfS hgS hfT hgT j).mp hj
  exact IsoFrameUnits.gauge_coefficient_independent _ _ _ _ _ _
    (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero F G i.1.1 i.1.2 s hi'.1.1 hi'.1.2)
    (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero F G j.1.1 j.1.2 s hj'.1.1 hj'.1.2)
    (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ne_zero F G i.2.1 i.2.2 t hi'.2.1 hi'.2.2) H

end

end OAI.RepresentationTheory.Theta.Geometric.IsoGaugeCompatibility
