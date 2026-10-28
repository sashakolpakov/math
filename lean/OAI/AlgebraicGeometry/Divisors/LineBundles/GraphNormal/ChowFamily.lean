import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ChowJointDetection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Chow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.PointChowAllGrades
import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.DimensionDetection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.MapCharacterization

/-! # Chow Family -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ChowFamily.BundleCycles

noncomputable section

/-! The actual graph-normal Chow family descends every singular-support
principal relation and is jointly injective across all dimension grades. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ)

theorem graphNormalPointChow_relations (d : ℕ) : Chow.BundleCycles.rationalEquivalenceQ X p ≤
    LinearMap.ker ((Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d).comp
      ((Graph.Chow.BundleCycles.graphNormalPointPullback f).comp (Chow.BundleCycles.projectiveCyclePointMap X p))) := by
  apply Submodule.span_le.mpr
  rintro z ⟨W, hW, g, hg, hz⟩
  change Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d
    (Graph.Chow.BundleCycles.graphNormalPointPullback f (Chow.BundleCycles.projectiveCyclePointMap X p z)) = 0
  rw [Chow.BundleCycles.projectiveCyclePointMap_apply, hz]
  change Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d
    (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Graph.Chow.BundleCycles.graphNormalProjection f) (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g)) = 0
  rw [AffineSpacePrincipalRelations.BundleCycles.locallyAffineSpaceCycleExtension_principal (Graph.Chow.BundleCycles.graphNormalProjection f)
    (Affine.SpaceChartBaseChange.BundleCycles.graphNormalCone_hasAffineSpaceCharts f) W g hg]
  exact Principal.PointChowAllGrades.BundleCycles.pointCycleToChowQ_principal_all_grades (Graph.Chow.BundleCycles.graphConeStructureMap f) d _ _

def graphNormalChowFamily : Geometric.MapCharacterization.BundleCycles.GraphNormalChowFamily f p := fun d =>
  (Chow.BundleCycles.rationalEquivalenceQ X p).liftQ ((Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d).comp
    ((Graph.Chow.BundleCycles.graphNormalPointPullback f).comp (Chow.BundleCycles.projectiveCyclePointMap X p))) (graphNormalPointChow_relations f p d)

theorem graphNormalChowFamily_cycle (d : ℕ) (z : X.RationalDimensionCycle p) :
    graphNormalChowFamily f p d (Chow.BundleCycles.cycleToChowQ X p z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d (Graph.Chow.BundleCycles.graphNormalPointPullback f (Chow.BundleCycles.pointCycle X p z)) := by
  change Point.CycleChow.BundleCycles.pointCycleToChowQ (Graph.Chow.BundleCycles.graphConeStructureMap f) d
    (Graph.Chow.BundleCycles.graphNormalPointPullback f (Chow.BundleCycles.projectiveCyclePointMap X p z)) = _
  rw [Chow.BundleCycles.projectiveCyclePointMap_apply]

theorem graphNormalChowFamily_isGeometric : Geometric.MapCharacterization.BundleCycles.IsGraphNormalChowFamily f p (graphNormalChowFamily f p) :=
  graphNormalChowFamily_cycle f p

theorem graphNormalChowFamily_joint_injective :
    Function.Injective (fun α : Chow.BundleCycles.ChowQ X p => fun d : ℕ => graphNormalChowFamily f p d α) := by
  intro α β h
  obtain ⟨z, rfl⟩ := Chow.BundleCycles.cycleToChowQ_surjective X p α
  obtain ⟨w, rfl⟩ := Chow.BundleCycles.cycleToChowQ_surjective X p β
  apply ProjectiveChow.DimensionDetection.BundleCycles.projectiveChow_dimensionClasses_joint_equal X p z w
  apply ChowJointDetection.BundleCycles.graphNormalPointChow_joint_equal f
  intro d
  simpa only [graphNormalChowFamily_cycle] using congrFun h d

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ChowFamily.BundleCycles
