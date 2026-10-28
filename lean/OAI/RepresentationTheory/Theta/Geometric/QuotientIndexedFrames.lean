import OAI.RepresentationTheory.Theta.Geometric.ProductFrames
import OAI.RepresentationTheory.Theta.Geometric.ProductValues
import OAI.RepresentationTheory.Theta.Geometric.FrameTransitionUnitCoherence
import OAI.RepresentationTheory.Theta.Geometric.ConsecutiveGauge

/-! # Quotient Indexed Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.QuotientIndexedFrames

noncomputable section

section

/-! The actual native quotient-frame transition has the ratio of the
original consecutive analytic gauges as its value. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

set_option backward.isDefEq.respectTransparency false in
theorem thetaQuotientFrameOn_transitionUnit_value (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (g : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z : Φ.space)
    (hf : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk z)))
    (hg : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk z)))
    (i k : Fin (F.projectiveDimension + 1)) (j l : Fin (G.projectiveDimension + 1))
    (W : X.left.Opens)
    (hF : W ≤ f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
    (hG : W ≤ g.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) j l)
    (hp : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W) :
    Complex.SectionEvaluation.complexSectionValue p.left W hp
      (IntrinsicFrame.TransitionUnits.frameTransitionUnit (AlgebraicQuotient.algebraicThetaQuotient f.left g.left).sheaf W
        (ProductFrames.thetaQuotientFrameOn f.left g.left i j W
          (hF.trans (f.left.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) i k)))
          (hG.trans (g.left.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) j l))))
        (ProductFrames.thetaQuotientFrameOn f.left g.left k l W
          (hF.trans (f.left.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := ℂ) i k)))
          (hG.trans (g.left.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := ℂ) j l)))) :
        Γ(X.left, W)) = ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G k l z / ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i j z := by
  have ht := FrameTransitionUnitCoherence.frameTransitionUnit_unique (AlgebraicQuotient.algebraicThetaQuotient f.left g.left).sheaf W _ _ _
    (ProductFrames.thetaQuotientFrameOn_transition f.left g.left i k j l W hF hG)
  rw [← ht]
  simp only [Units.val_mul, map_mul, map_units_inv, PowerGaugeCover.restrictRegularUnit_value]
  rw [ProductValues.thetaTransitionUnit_value_of_point G g p z hg j l,
    ProductValues.thetaTransitionUnit_value_of_point F f p z hf i k, ← div_eq_mul_inv]
  exact (ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge_ratio F G i k j l z).symm

end

/-! Paired coordinates for native quotient frames and their evaluated
transition functions on arbitrary common subopens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta

abbrev ThetaFrameIndex (n m : ℕ) := Fin (n + 1) × Fin (m + 1)

def thetaQuotientIndexedFrame {X : Scheme} {n m : ℕ}
    (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m)
    (i : ThetaFrameIndex n m) (W : X.Opens) (h : W ≤ ProductFrames.thetaQuotientOpen f g i.1 i.2) :
    (AlgebraicQuotient.algebraicThetaQuotient f g).sheaf.restrict W.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule W.toScheme :=
  ProductFrames.thetaQuotientFrameOn f g i.1 i.2 W (h.trans inf_le_left) (h.trans inf_le_right)

theorem thetaQuotientIndexedFrame_restrict {X : Scheme} {n m : ℕ}
    (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m)
    (i : ThetaFrameIndex n m) {U W : X.Opens} (h : W ≤ U)
    (hU : U ≤ ProductFrames.thetaQuotientOpen f g i.1 i.2) :
    AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h (thetaQuotientIndexedFrame f g i U hU) =
      thetaQuotientIndexedFrame f g i W (h.trans hU) :=
  ProductFrames.thetaQuotientFrameOn_restrict f g i.1 i.2 h _ _

theorem thetaQuotientIndexedFrame_transition_value
    {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (g : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z : Φ.space)
    (hf : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap (QuotientAddGroup.mk z)))
    (hg : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g p = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap (QuotientAddGroup.mk z)))
    (i j : ThetaFrameIndex F.projectiveDimension G.projectiveDimension) (W : X.left.Opens)
    (hi : W ≤ ProductFrames.thetaQuotientOpen f.left g.left i.1 i.2)
    (hj : W ≤ ProductFrames.thetaQuotientOpen f.left g.left j.1 j.2)
    (hp : p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ W) :
    Complex.SectionEvaluation.complexSectionValue p.left W hp
      (IntrinsicFrame.TransitionUnits.frameTransitionUnit (AlgebraicQuotient.algebraicThetaQuotient f.left g.left).sheaf W
        (thetaQuotientIndexedFrame f.left g.left i W hi)
        (thetaQuotientIndexedFrame f.left g.left j W hj) : Γ(X.left, W)) =
      ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G j.1 j.2 z / ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge F G i.1 i.2 z := by
  have hF : W ≤ f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i.1 j.1 := by
    rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
    exact le_inf (hi.trans inf_le_left) (hj.trans inf_le_left)
  have hG : W ≤ g.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i.2 j.2 := by
    rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
    exact le_inf (hi.trans inf_le_right) (hj.trans inf_le_right)
  exact thetaQuotientFrameOn_transitionUnit_value F G f g p z hf hg i.1 j.1 i.2 j.2 W hF hG hp

end

end OAI.RepresentationTheory.Theta.Geometric.QuotientIndexedFrames
