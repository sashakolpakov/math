import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ZeroLocus
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow

/-! # Zero Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ZeroChow.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual zero-section Cartier intersection on affine-line Chow groups -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

theorem affineLineZeroStructureMap_eq :
    Space.BundleCycles.affineLineZeroSection X ≫ (Charts.BundleCycles.affineLineProjection X ≫ f) = f :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ f) (Space.BundleCycles.affineLineZeroSection_projection X)).trans (Category.id_comp f))

variable [AlgebraicGeometry.IsNoetherian X] [LocallyOfFiniteType f]

def affineLineZeroChowMap (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ f d :=
  (DimensionChow.BundleCycles.dimensionChowTransport (affineLineZeroStructureMap_eq X f) d).comp
    (Principal.CartierChow.BundleCycles.principalCartierChowMap (Space.BundleCycles.affineLineZeroSection X) (Space.BundleCycles.affineLineCoordinate X)
      (ZeroLocus.BundleCycles.affineLineZeroSection_range X) (Charts.BundleCycles.affineLineProjection X ≫ f) d)

theorem affineLineZeroChowMap_cycle (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) →₀ ℚ) :
    affineLineZeroChowMap X f d (DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) z) =
      DimensionChow.BundleCycles.dimensionChowTransport (affineLineZeroStructureMap_eq X f) d
        (Principal.CartierFiber.BundleCycles.principalCartierFiberClassMap (Space.BundleCycles.affineLineZeroSection X) (Space.BundleCycles.affineLineCoordinate X)
          (Charts.BundleCycles.affineLineProjection X ≫ f) d z) := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ZeroChow.BundleCycles
