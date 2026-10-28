import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowPointClass

/-! # Chow Open Square -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowOpenSquare.BundleCycles

noncomputable section

/-! Genuine Chow extension from affine-space source charts commutes
with squares of open immersions, including partial fiber opens. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X E' U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian E']
    [AlgebraicGeometry.IsNoetherian U]
    (p : E ⟶ X) (q : E' ⟶ U) [Smooth p] [Smooth q]
    [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : U ⟶ X) (j : E' ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j]
    (hs : q ≫ i = j ≫ p) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)

theorem affineSpaceSourceChowExtension_openSquare (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    DimensionChow.BundleCycles.dimensionChowTransport (show j ≫ (p ≫ f) = q ≫ (i ≫ f) by
      rw [← Category.assoc, ← hs, Category.assoc]) (d + r)
      (Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + r) (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d α)) =
      AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension q (i ≫ f) r hq d (Open.ChowRestriction.BundleCycles.openChowRestriction i f d α) := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d α
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z, AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass,
    Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass, Point.ChowTransport.BundleCycles.dimensionChowTransport_pointCycle,
    Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass, AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass,
    Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_openSquare p q i j hs]

theorem affineSpaceSourceChowExtension_openOver
    {E X U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian U]
    (p : E ⟶ X) (q : U ⟶ X) [Smooth p] [Smooth q]
    [GeometricallyIntegral p] [GeometricallyIntegral q]
    (j : U ⟶ E) [IsOpenImmersion j] (hj : j ≫ p = q)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)
    (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    DimensionChow.BundleCycles.dimensionChowTransport (show j ≫ (p ≫ f) = q ≫ f by rw [← Category.assoc, hj]) (d + r)
      (Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + r) (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d α)) =
      AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension q f r hq d α := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d α
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z, AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass,
    Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass, Point.ChowTransport.BundleCycles.dimensionChowTransport_pointCycle,
    AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass]
  have hs : q ≫ 𝟙 X = j ≫ p := by rw [Category.comp_id, hj]
  rw [Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_openSquare p q (𝟙 X) j hs]
  congr 2
  ext x
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowOpenSquare.BundleCycles
