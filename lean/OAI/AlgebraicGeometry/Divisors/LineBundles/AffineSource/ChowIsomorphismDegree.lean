import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowIsoPushforward

/-! # Chow Isomorphism Degree -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowIsomorphismDegree.BundleCycles

noncomputable section

/-! The degree-zero calculation for an isomorphic projection uses
the actual fiber-generic extension and residue-weighted pushforward. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [E.IsSeparated] [X.IsSeparated]
    (p : E ⟶ X) [IsIso p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p 0)

theorem affineSpaceSourceChowExtension_isomorphism_degree (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f 0 hp d α) = α := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d α
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z, AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass]
  change Proper.ChowNe.BundleCycles.properChowPushforward p f d (Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d
    (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z))) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z)
  rw [Proper.ChowNe.BundleCycles.properChowPushforward_pointClass p f d, IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion p]
  apply congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ f d)
  change Finsupp.mapDomain p (Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) _) = _
  rw [← Finsupp.mapDomain_comp]
  have he : (p : E → X) ∘ Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p = id := by
    funext x
    exact Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection p x
  rw [he, Finsupp.mapDomain_id]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowIsomorphismDegree.BundleCycles
