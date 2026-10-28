import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedAbsoluteClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteProjection

/-! # Class Degree Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ClassDegreePullback.BundleCycles

noncomputable section

/-! Transport between the two standard degree conventions commutes with genuine Betti pullback of every finite graded cycle class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) (d p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)

theorem schemeGradedCycleClass_betti_degreeTransport (c : GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom d →₀ ℚ) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) i (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass Y d p hd c) =
      Scheme.GradedAbsoluteClass.BundleCycles.schemeBettiDegreeEquiv X (two_mul p)
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) i (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass Y d p hd c)) := by
  rw [Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass_eq_degreeEquiv, LinearMap.comp_apply]
  change Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) i
    (Scheme.GradedAbsoluteClass.BundleCycles.schemeBettiDegreeEquiv Y (two_mul p) (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass Y d p hd c)) = _
  rw [Scheme.GradedAbsoluteClass.BundleCycles.schemeBettiDegreeEquiv_apply, Scheme.GradedAbsoluteClass.BundleCycles.schemeBettiDegreeEquiv_apply]
  exact Scheme.AbsoluteProjection.BundleCycles.schemeBettiMap_cast (ModuleCat.of ℚ ℚ) i (two_mul p) _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ClassDegreePullback.BundleCycles
