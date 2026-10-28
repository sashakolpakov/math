import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointClosedMap
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeImmersionPointTopology

/-! # Open Pullback Points -/

namespace OAI.RepresentationTheory.Theta.Geometric.OpenPullbackPoints

noncomputable section

/-! Pulling a continuous point map into an open component gives an
actual continuous map to the scheme-theoretic pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem continuous_pullbackLift_of_open
    {M : Type*} [TopologicalSpace M] {X Y Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion g.left]
    (a : M → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (b : M → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (h : ∀ x, a x ≫ f = b x ≫ g) (ha : Continuous a) :
    Continuous (fun x => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackLift f g (a x) (b x) (h x)) := by
  let : IsOpenImmersion (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g).left :=
    inferInstanceAs (IsOpenImmersion (CategoryTheory.Limits.pullback.fst f.left g.left))
  apply (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g)).isEmbedding.continuous_iff.mpr
  change Continuous (fun x => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackLift f g (a x) (b x) (h x) ≫ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f g)
  simpa only [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackLift_toLeft] using ha

end

end OAI.RepresentationTheory.Theta.Geometric.OpenPullbackPoints
