import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowIsomorphismDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.Filtration

/-! # Chow Isomorphism Inverse -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowIsomorphismInverse.BundleCycles

noncomputable section

/-! An isomorphic projection has its actual inverse Chow fiber
extension; it supplies the zero-rank case of projective generation. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] [X.IsSeparated] (p : E ⟶ X) [IsIso p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p 0)

theorem affineSpaceSourceChowExtension_isomorphism_rightInverse (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d) :
    AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f 0 hp d (Proper.ChowNe.BundleCycles.properChowPushforward p f d α) = α := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (p ≫ f) d α
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion (p ≫ f) d z, Proper.ChowNe.BundleCycles.properChowPushforward_pointClass,
    AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass, IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion p]
  change Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d
    (Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) (Finsupp.mapDomain p (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (p ≫ f) d z))) = _
  rw [← Finsupp.mapDomain_comp]
  have he : Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p ∘ (p : E → X) = id := by
    funext x
    apply p.isOpenEmbedding.injective
    exact Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection p (p x)
  rw [he, Finsupp.mapDomain_id]

theorem projectiveChowGenerated_of_isIso (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d) :
    α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated p f 0 hp L d := by
  have H := ProjectiveChow.Filtration.BundleCycles.affineSpaceSourceChowExtension_mem_projectiveGenerated p f 0 hp L d (Proper.ChowNe.BundleCycles.properChowPushforward p f d α)
  rw [affineSpaceSourceChowExtension_isomorphism_rightInverse] at H
  exact H

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowIsomorphismInverse.BundleCycles
