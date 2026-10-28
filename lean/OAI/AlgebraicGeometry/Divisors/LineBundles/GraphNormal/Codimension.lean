import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ConeCodimensionChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.CodimensionSet

/-! # Codimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.Codimension.BundleCycles

noncomputable section

/-! Actual normal extension commutes with codimension selection on
finite point cycles, with no constant-rank assumption. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ)

theorem graphNormalPointPullback_single (x : X.carrier) (a : ℚ) :
    Graph.Chow.BundleCycles.graphNormalPointPullback f (Finsupp.single x a) =
      Finsupp.single (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Graph.Chow.BundleCycles.graphNormalProjection f) x) a :=
  Finsupp.mapDomain_single

theorem graphNormalPointPullback_codimensionPart (z : X.carrier →₀ ℚ) :
    Graph.Chow.BundleCycles.graphNormalPointPullback f (Chow.BundleCycles.pointCycle X p (Projective.CodimensionPointClass.BundleCycles.projectiveCodimensionComponent X p z)) =
      Graph.SpecializationCycleCodimension.BundleCycles.graphConeCodimensionPart f p (Graph.Chow.BundleCycles.graphNormalPointPullback f z) := by
  rw [Projective.CodimensionSet.BundleCycles.pointCycle_projectiveCodimensionComponent]
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | single x a =>
    by_cases hx : X.supportCodimension (irreducibleSetEquivPoints.symm x) = p
    · rw [Point.CycleSet.BundleCycles.pointCycleSetPart_single_mem {u | X.supportCodimension (irreducibleSetEquivPoints.symm u) = p} x a hx,
        graphNormalPointPullback_single]
      exact (Point.CycleSet.BundleCycles.pointCycleSetPart_single_mem {y | Graph.SpecializationPointCodimension.BundleCycles.GraphConePointHasCodimension f p y} _ a
        ((Graph.ConeCodimensionChow.BundleCycles.graphNormal_genericPoint_codimension_iff f p x).mpr hx)).symm
    · rw [Point.CycleSet.BundleCycles.pointCycleSetPart_single_notMem {u | X.supportCodimension (irreducibleSetEquivPoints.symm u) = p} x a hx,
        map_zero, graphNormalPointPullback_single]
      exact (Point.CycleSet.BundleCycles.pointCycleSetPart_single_notMem {y | Graph.SpecializationPointCodimension.BundleCycles.GraphConePointHasCodimension f p y} _ a
        (fun h => hx ((Graph.ConeCodimensionChow.BundleCycles.graphNormal_genericPoint_codimension_iff f p x).mp h))).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.Codimension.BundleCycles
