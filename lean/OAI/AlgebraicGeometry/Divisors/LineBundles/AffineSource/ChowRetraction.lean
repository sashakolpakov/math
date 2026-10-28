import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChowTransportLaws

/-! # Chow Retraction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowRetraction.BundleCycles

noncomputable section

/-! An actual affine-space open over the entire base gives a Chow
retraction of fiber extension. This applies to every finite free projective bundle. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (ι : Type) [Finite ι]
    (h : LineBundles.AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p (Nat.card ι))
    (j : AffineSpace ι X ⟶ E) [IsOpenImmersion j]
    (hj : j ≫ p = (AffineSpace ι X ↘ X))

omit [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
  [Smooth p] [GeometricallyIntegral p] [LocallyOfFiniteType f] [Finite ι] [IsOpenImmersion j] in
include hj in
theorem affineSourceChart_structureMap :
    j ≫ (p ≫ f) = (AffineSpace ι X ↘ X) ≫ f := by
  rw [← Category.assoc, hj]

theorem affineSourceChowExtension_restrict (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d) :
    DimensionChow.BundleCycles.dimensionChowTransport (affineSourceChart_structureMap p f ι j hj) (d + Nat.card ι)
      (Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + Nat.card ι)
        (LineBundles.AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (Nat.card ι) h d a)) =
      FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv X f ι d a := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d a
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z, LineBundles.AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass,
    Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass, Point.ChowTransport.BundleCycles.dimensionChowTransport_pointCycle,
    FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv_pointClass]
  have hs : (AffineSpace ι X ↘ X) ≫ 𝟙 X = j ≫ p := by rw [Category.comp_id, hj]
  rw [Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_openSquare p (AffineSpace ι X ↘ X) (𝟙 X) j hs]
  congr 2
  ext x
  rfl

def affineSourceChowRetraction (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) (d + Nat.card ι) →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ f d :=
  ((FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv X f ι d).symm.toLinearMap.comp
    (DimensionChow.BundleCycles.dimensionChowTransport (affineSourceChart_structureMap p f ι j hj) (d + Nat.card ι))).comp
      (Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + Nat.card ι))

theorem affineSourceChowRetraction_extension (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d) :
    affineSourceChowRetraction p f ι j hj d
      (LineBundles.AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (Nat.card ι) h d a) = a := by
  change (FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv X f ι d).symm
    (DimensionChow.BundleCycles.dimensionChowTransport _ _ (Open.ChowRestriction.BundleCycles.openChowRestriction _ _ _ _)) = a
  rw [affineSourceChowExtension_restrict p f ι h j hj]
  exact (FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv X f ι d).symm_apply_apply a

include j hj in
theorem affineSourceChowExtension_injective (d : ℕ) :
    Function.Injective (LineBundles.AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (Nat.card ι) h d) :=
  Function.LeftInverse.injective (affineSourceChowRetraction_extension p f ι h j hj d)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowRetraction.BundleCycles
