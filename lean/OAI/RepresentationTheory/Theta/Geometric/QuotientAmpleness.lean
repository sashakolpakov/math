import OAI.RepresentationTheory.Theta.Geometric.HyperplanePullbackAmpleness
import OAI.RepresentationTheory.Theta.Geometric.CanonicalPowerIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerStability

/-! # Quotient Ampleness -/

namespace OAI.RepresentationTheory.Theta.Geometric.QuotientAmpleness

noncomputable section

/-! The canonical consecutive theta quotient is ample as an actual algebraic
line bundle, by its constructed positive-power isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem thetaQuotient_isAmple_of_power_iso {X : Scheme} [CompactSpace X] {n m : ℕ}
    (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m) [IsClosedImmersion f]
    (k : ℕ) (hk : 0 < k)
    (e : AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule (AlgebraicQuotient.algebraicThetaQuotient f g).sheaf k ≅
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n 1)).sheaf) :
    (AlgebraicQuotient.algebraicThetaQuotient f g).IsAmple :=
  AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsAmple.of_tensorPower k hk ((HyperplanePullbackAmpleness.hyperplanePullback_isAmple f).of_iso e.symm)

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

theorem canonicalThetaQuotient_isAmple [LocallyOfFiniteType X.hom] [IsReduced X.left] [CompactSpace X.left]
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hF : 0 < F.degree) (hdeg : G.degree = F.degree + 1)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.commonPower G).projectiveDimension))
    (fF : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (fG : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension)) [IsClosedImmersion fF.left]
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hsurj : Function.Surjective e)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.commonPower G).projectiveDimension ((F.commonPower G).projectiveMap t))
    (heF : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fF (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t))
    (heG : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fG (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension (G.projectiveMap t)) :
    (AlgebraicQuotient.algebraicThetaQuotient fF.left fG.left).IsAmple := by
  obtain ⟨a⟩ := CanonicalPowerIso.canonicalThetaQuotientPower_iso F G hF hdeg f fF fG e hsurj he heF heG
  exact thetaQuotient_isAmple_of_power_iso fF.left fG.left F.degree hF a

end

end OAI.RepresentationTheory.Theta.Geometric.QuotientAmpleness
