import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowOpenSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowFunctoriality

/-! # Chow Iso Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowIsoPushforward.BundleCycles

noncomputable section

/-! Isomorphic relative schemes have the same actual Chow
fiber extension after pushforward through the scheme isomorphism. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

theorem affineSpaceSourceChowExtension_isoPushforward
    {E E' X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian E']
    [AlgebraicGeometry.IsNoetherian X] [E.IsSeparated] [E'.IsSeparated]
    (p : E ⟶ X) (q : E' ⟶ X) [Smooth p] [Smooth q]
    [GeometricallyIntegral p] [GeometricallyIntegral q]
    (j : E' ⟶ E) [IsIso j] (hj : j ≫ p = q)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)
    (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowFunctoriality.BundleCycles.properChowPushforwardOver j (q ≫ f) (p ≫ f) (by rw [← Category.assoc, hj]) (d + r)
      (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension q f r hq d α) = AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d α := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d α
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z, AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass,
    Proper.ChowFunctoriality.BundleCycles.properChowPushforwardOver_pointClass, AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass,
    IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion j]
  apply congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) (d + r))
  change Finsupp.mapDomain j (Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint q) _) =
    Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) _
  rw [← Finsupp.mapDomain_comp]
  apply congrArg (fun k => Finsupp.mapDomain k (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z))
  funext x
  exact Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_openSquare p q (𝟙 X) j (by rw [Category.comp_id, hj]) x

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowIsoPushforward.BundleCycles
